#!/usr/bin/env python3
"""
Synchronisation SIA -> dépôt NPF-Q400-VAC.

Périmètre NPF v16.50 :
- tous les aérodromes OACI affichés sur la carte NPF ;
- 446 codes OACI uniques issus de la table PIAF métropole + Corse ;
- les pélicandromes permanents et aérodromes sélectionnables conservent leur type NPF ;
- les autres terrains affichés sont classés "aerodrome_carte".

Sélection SIA stricte :
- libellé exact : AIP - AD-2.LFXX.pdf
- catégorie exacte : AIP Atlas VAC
- aucun SUP AIP ni autre document associé au terrain (ADC, AOC, APDC, IAC... de
  la catégorie "AIP FRANCE" sont ignorés)
- depuis le cycle 01_OCT_2026, la recherche SIA renvoie aussi toutes les cartes eAIP
  du terrain : la VAC est souvent en dernière page. Toutes les pages de l'onglet
  "Information aéronautique" sont donc lues (page 1, puis de la dernière vers la 2e),
  et l'absence de VAC n'est retenue qu'après lecture complète et cohérente des pages.

Principes de sécurité :
- la synchronisation travaille d'abord en mémoire / fichiers temporaires ;
- le dépôt n'est modifié qu'après validation de tous les téléchargements nécessaires ;
- en cas d'erreur technique, le script échoue avant toute modification du manifeste ;
- une ancienne VAC déjà publiée n'est jamais supprimée automatiquement ;
- si une VAC n'est plus publiée par le SIA, le fichier historique peut rester sur GitHub
  mais le manifeste la marque indisponible afin que NPF ne l'affiche plus ;
- les mises à jour applicatives compareront les SHA-256 ;
- si une VAC disponible dans le manifeste actuel n'est plus trouvée sur le site du SIA,
  rien n'est publié et le script échoue après avoir contrôlé les 446 terrains, sauf
  --accept-removals (case "accepter les retraits" du workflow).

Optimisation :
- un cycle témoin est résolu via LFBD ;
- si le cycle SIA est identique au cycle déjà enregistré ET que le périmètre est déjà
  complet, le script sort sans tout recontrôler, sauf --force ;
- si le périmètre du manifeste est ancien (123 terrains par exemple), une synchronisation
  complète est déclenchée automatiquement même si le cycle SIA est inchangé ;
- lors d'un nouveau cycle, toutes les VAC du périmètre sont revalidées ;
  seuls les PDF dont le SHA-256 change sont remplacés dans vac/.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urljoin

import requests
from bs4 import BeautifulSoup

SIA = "https://www.sia.aviation-civile.gouv.fr"
TARGET_CATEGORY = "AIP Atlas VAC"
SENTINEL_ICAO = "LFBD"

RESULTS_TAB_ID = "document.result.tab1"
RESULTS_TAB_LABEL = "Information aéronautique"
RESULTS_PAGE_SIZE = 10
MAX_RESULT_PAGES = 40
HTTP_ATTEMPTS = 3

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/151 Safari/537.36 "
    "NPF-Q400-VAC-sync/1.2"
)

BASE_HEADERS = {
    "User-Agent": USER_AGENT,
    "Accept-Language": "fr-FR,fr;q=0.9,en;q=0.7",
    "Cache-Control": "no-cache",
}

NPF_AIRPORTS = [
    {'oaci': 'LFBP', 'name': 'Pau-Pyrénées', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFLS', 'name': 'Grenoble-Isère', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRQ', 'name': 'Quimper-Pluguffan', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFOT', 'name': 'Tours-Val de Loire', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFPG', 'name': 'Paris-Charles-de-Gaulle', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFPO', 'name': 'Paris-Orly', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRC', 'name': 'Cherbourg-Manche', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRH', 'name': 'Lorient-Bretagne-Sud', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFTW', 'name': 'Nîmes-Garons', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFBE', 'name': 'Bergerac-Roumanière', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFBO', 'name': 'Toulouse-Blagnac', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFBZ', 'name': 'Biarritz-Pays Basque', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFKB', 'name': 'Bastia-Poretta', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFLL', 'name': 'Lyon-Saint Exupéry', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFLX', 'name': 'Châteauroux-Déols', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFML', 'name': 'Marseille-Provence', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFOH', 'name': 'Le Havre-Octeville', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFPB', 'name': 'Paris-Le Bourget', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRD', 'name': 'Dinard-Pleurtuit-Saint-Malo', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRK', 'name': 'Caen-Carpiquet', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRN', 'name': 'Rennes-Saint-Jacques', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFSD', 'name': 'Dijon-Longvic', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFBD', 'name': 'Bordeaux-Mérignac', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFRB', 'name': 'Brest-Bretagne', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFGJ', 'name': 'Dole-Tavaux', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFLB', 'name': 'Chambéry-Savoie', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFLC', 'name': 'Clermont-Ferrand-Auvergne', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFMV', 'name': 'Avignon-Provence', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFOP', 'name': 'Rouen-Vallée de Seine', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFBF', 'name': 'Toulouse-Francazal', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFMT', 'name': 'Montpellier-Méditerranée', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFMU', 'name': 'Béziers-Vias', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFQQ', 'name': 'Lille-Lesquin', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRS', 'name': 'Nantes-Atlantique', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFAB', 'name': 'DIEPPE SAINT AUBIN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAI', 'name': 'NANGIS LES LOGES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAK', 'name': 'DUNKERQUE LES MOERES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAL', 'name': 'LA FLECHE THOREE LES PINS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAM', 'name': 'BERCK SUR MER', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAU', 'name': 'VAUVILLE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFBG', 'name': 'Cognac-Châteaubernard', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFBN', 'name': 'Niort-Souché', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFBR', 'name': 'MURET LHERM', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFBS', 'name': 'BISCARROSSE PARENTIS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCD', 'name': 'ANDERNOS LES BAINS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCH', 'name': 'ARCACHON LA TESTE DE BUCH', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCJ', 'name': 'JONZAC NEULLES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCN', 'name': 'NOGARO', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCO', 'name': 'OLORON HERRERE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCP', 'name': 'PONS AVY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCQ', 'name': 'GRAULHET MONTDRAGON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCS', 'name': 'BORDEAUX LEOGNAN SAUCATS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCT', 'name': 'THOUARS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCX', 'name': 'CASTELSARRASIN MOISSAC', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCY', 'name': 'ROYAN MEDIS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDA', 'name': "AIRE SUR L'ADOUR", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDC', 'name': 'MONTENDRE MARCILLAC', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDF', 'name': 'SAINTE FOY LA GRANDE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDG', 'name': 'GAILLAC LISLE SUR TARN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDH', 'name': 'AUCH LAMOTHE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDI', 'name': 'LIBOURNE ARTIGUES DE LUSSAC', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDL', 'name': 'LOUDUN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDM', 'name': 'MARMANDE VIRAZEIL', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDN', 'name': 'Rochefort-Saint-Agnant', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFDP', 'name': "SAINT PIERRE D'OLERON", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDQ', 'name': 'CASTELNAU MAGNOAC', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDR', 'name': 'LA REOLE FLOUDES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDT', 'name': 'TARBES LALOUBERE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDU', 'name': 'LESPARRE SAINT LAURENT MEDOC', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDW', 'name': 'CHAUVIGNY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDY', 'name': 'BORDEAUX YVRAC', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEF', 'name': 'AMBOISE DIERRE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEJ', 'name': 'CHATEAUROUX VILLERS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEK', 'name': 'ISSOUDUN LE FAY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEL', 'name': 'LE BLANC', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEN', 'name': 'TOURS SORIGNY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEV', 'name': 'GRAY SAINT ADRIEN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEY', 'name': "ILE D'YEU", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFC', 'name': 'MANTES CHERENCE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFD', 'name': "SAINT ANDRE DE L'EURE", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFE', 'name': 'ENGHIEN MOISSELLES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFK', 'name': 'FONTENAY LE COMTE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFQ', 'name': 'LA FERTE ALAIS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFU', 'name': 'CHATEAUNEUF SUR CHER', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFV', 'name': 'VIERZON MEREAU', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFW', 'name': 'MONTAIGU SAINT GEORGES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFX', 'name': 'TOURNUS CUISERY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFY', 'name': 'ETREPAGNY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGB', 'name': 'MULHOUSE HABSHEIM', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGF', 'name': 'BEAUNE CHALLANGES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGG', 'name': 'BELFORT CHAUX', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGI', 'name': 'DIJON DAROIS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGL', 'name': 'LONS LE SAUNIER COURLAOUX', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGO', 'name': 'PONT SUR YONNE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGZ', 'name': 'NUITS SAINT GEORGES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHC', 'name': 'PEROUGES MEXIMIEUX', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHD', 'name': 'PIERRELATTE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHE', 'name': 'ROMANS SAINT PAUL', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHF', 'name': 'RUOMS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHG', 'name': "SAINT CHAMOND L'HORME", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHH', 'name': 'VIENNE REVENTIN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHI', 'name': 'MORESTEL', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHJ', 'name': 'LYON CORBAS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHV', 'name': 'VILLEFRANCHE TARARE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHW', 'name': 'BELLEVILLE VILLIE MORGON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHY', 'name': 'MOULINS MONTBEUGNY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFIB', 'name': 'BELVES SAINT PARDOUX', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFIH', 'name': 'CHALAIS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFIL', 'name': 'RION DES LANDES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFIM', 'name': 'SAINT GAUDENS MONTREJEAU', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFIT', 'name': 'TOULOUSE BOURG SAINT BERNARD', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFIX', 'name': 'ITXASSOU', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFIY', 'name': "SAINT JEAN D'ANGELY SAINT DENIS DU PIN", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFJD', 'name': 'CORLIER', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFJE', 'name': 'LA MOTTE CHALANCON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFJF', 'name': 'AUBENASSON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFJI', 'name': 'MARENNES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFJR', 'name': 'Angers-Marcé', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFJT', 'name': 'TOURS LE LOUROUX', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFJU', 'name': 'LURCY LEVIS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFJV', 'name': 'LASCLAVERIES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFKE', 'name': 'SAINT JEAN EN ROYANS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFKH', 'name': "SAINT JEAN D'AVELANNE", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFKK', 'name': 'MONTMEILLEUR', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFKL', 'name': 'LYON BRINDAS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFKP', 'name': 'LA TOUR DU PIN CESSIEU', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFKY', 'name': 'BELLEY-PEYRIEU', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFLD', 'name': 'Bourges', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFLE', 'name': 'CHAMBERY CHALLES LES EAUX', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFLG', 'name': 'GRENOBLE LE VERSOUD', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFLH', 'name': 'CHALON CHAMPFORGEUIL', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFLN', 'name': 'Saint-Yan', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFLO', 'name': 'Roanne-Renaison', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFLP', 'name': 'Annecy-Meythet', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFLQ', 'name': 'MONTELIMAR ANCONE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFLR', 'name': "SAINT RAMBERT D'ALBON", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFLU', 'name': 'Valence-Chabeuil', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFLZ', 'name': 'Le Puy-Loudes', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFME', 'name': 'NIMES COURBESSAC', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFMX', 'name': 'CHATEAU ARNOUX SAINT AUBAN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFMZ', 'name': 'LEZIGNAN CORBIERES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNA', 'name': 'GAP TALLARD', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNE', 'name': 'SALON EYGUIERES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNF', 'name': 'VINON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNH', 'name': 'CARPENTRAS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNJ', 'name': 'ASPRES SUR BUECH', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNL', 'name': 'SAINT MARTIN DE LONDRES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNN', 'name': 'NARBONNE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNP', 'name': 'PEZENAS NIZAS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNR', 'name': 'BERRE LA FARE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNS', 'name': 'SISTERON THEZE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNT', 'name': 'AVIGNON PUJAUT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNU', 'name': 'UZES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNV', 'name': 'VALREAS VISAN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNZ', 'name': 'LE MAZET DE ROMANIN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFOI', 'name': 'Abbeville', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFOM', 'name': 'LESSAY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFOO', 'name': "LES SABLES D'OLONNE TALMONT", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFOQ', 'name': 'Blois-Le Breuil', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFOU', 'name': 'Cholet-Le Pontreau', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFOV', 'name': 'Laval-Entrammes', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFOY', 'name': 'LE HAVRE SAINT ROMAIN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFOZ', 'name': "ORLEANS SAINT DENIS DE L'HOTEL", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPD', 'name': 'BERNAY SAINT MARTIN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPF', 'name': 'BEYNES THIVERVAL', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPH', 'name': 'CHELLES LE PIN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPL', 'name': 'LOGNES EMERAINVILLE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPQ', 'name': 'FONTENAY TRESIGNY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPU', 'name': 'MORET EPISY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPX', 'name': 'CHAVENAY VILLEPREUX', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPZ', 'name': "SAINT CYR L'ECOLE", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQG', 'name': 'NEVERS FOURCHAMBAULT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQN', 'name': 'Saint-Omer-Wizernes', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFQO', 'name': 'LILLE MARCQ EN BAROEUL', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQT', 'name': 'MERVILLE CALONNE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFRI', 'name': 'La Roche-sur-Yon-Les Ajoncs', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRM', 'name': 'Le Mans-Arnage', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRP', 'name': 'PLOERMEL LOYAT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFRU', 'name': 'Morlaix-Ploujean', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRV', 'name': 'Vannes-Meucon', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFRW', 'name': 'AVRANCHES LE VAL SAINT PERE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFSA', 'name': 'BESANCON THISE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFSM', 'name': 'MONTBELIARD COURCELLES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFSS', 'name': 'SAINT SULPICE DES LANDES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFTM', 'name': 'SERRES LA BATIE MONTSALEON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFTN', 'name': "LA GRAND'COMBE", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFTQ', 'name': 'CHATEAUBRIANT POUANCE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFXA', 'name': 'AMBERIEU', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFXB', 'name': 'SAINTES THENAC', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFXU', 'name': 'LES MUREAUX', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFYR', 'name': 'Romorantin-Pruniers', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFAC', 'name': 'CALAIS DUNKERQUE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAE', 'name': 'EU MERS LE TREPORT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAT', 'name': 'LE TOUQUET PARIS PLAGE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFBC', 'name': 'Cazaux', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFBH', 'name': 'La Rochelle-Île de Ré', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFBM', 'name': 'Mont-de-Marsan', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFBY', 'name': 'DAX SEYRESSE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCA', 'name': 'CHATELLERAULT TARGE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCI', 'name': 'ALBI LE SEQUESTRE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCK', 'name': 'CASTRES MAZAMET', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCL', 'name': 'TOULOUSE LASBORDES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCW', 'name': 'VILLENEUVE SUR LOT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCZ', 'name': 'MIMIZAN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDB', 'name': 'MONTAUBAN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDK', 'name': 'SOULAC SUR MER', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDX', 'name': 'FUMEL MONTAYRAL', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEA', 'name': 'BELLE ILE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEB', 'name': 'DINAN TRELIVAN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEC', 'name': 'OUESSANT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFED', 'name': 'PONTIVY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEH', 'name': 'AUBIGNY SUR NERE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEQ', 'name': 'QUIBERON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFER', 'name': 'REDON BAINS SUR OUST', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFES', 'name': 'GUISCRIFF SCAER', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFI', 'name': 'ANCENIS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGH', 'name': 'COSNE SUR LOIRE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHO', 'name': 'Aubenas-Ardèche Méridionale', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFHU', 'name': "L'ALPE D'HUEZ", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHX', 'name': 'LAPALISSE PERIGNY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFIR', 'name': 'REVEL MONTGEY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFIS', 'name': 'SAINT INGLEVERT LES DEUX CAPS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFIV', 'name': 'VENDAYS MONTALIVET', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFJB', 'name': 'MAULEON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFLM', 'name': 'MACON CHARNAY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFLV', 'name': 'Vichy-Charmeil', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFLY', 'name': 'Lyon-Bron', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFMA', 'name': 'AIX LES MILLES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFMG', 'name': 'MONTAGNE NOIRE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFMI', 'name': 'Istres-Le Tubé', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFMO', 'name': 'Orange-Caritat', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFMQ', 'name': 'Le Castellet', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFMS', 'name': 'ALES CEVENNES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFMW', 'name': 'CASTELNAUDARY VILLENEUVE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFMY', 'name': 'Salon-de-Provence', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFNG', 'name': 'MONTPELLIER CANDILLARGUES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFOA', 'name': 'Avord', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFOD', 'name': 'SAUMUR SAINT FLORENT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFOE', 'name': 'Évreux-Fauville', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFPM', 'name': 'Melun-Villaroche', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFPN', 'name': 'TOUSSUS LE NOBLE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPT', 'name': 'PONTOISE CORMEILLES EN VEXIN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPV', 'name': 'Villacoublay-Vélizy', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFPY', 'name': 'BRETIGNY SUR ORGE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQM', 'name': 'BESANCON LA VEZE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFRE', 'name': 'La Baule-Escoublac', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRF', 'name': 'Granville-Mont-Saint-Michel', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRJ', 'name': 'Landivisiau', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRL', 'name': 'Lanvéoc-Poulmic', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRO', 'name': 'Lannion-Côte de Granit Rose', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRT', 'name': 'Saint-Nazaire-Montoir', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFRZ', 'name': 'Saint-Nazaire-Montoir', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFSC', 'name': 'COLMAR-MEYENHEIM', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFSQ', 'name': 'Luxeuil-Saint-Sauveur', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFTH', 'name': 'Toulon-Hyères', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFXI', 'name': 'SAINT CHRISTOL', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFXQ', 'name': 'COETQUIDAN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFYH', 'name': 'BROYE LES PESMES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFBT', 'name': 'Tarbes-Lourdes-Pyrénées', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFMP', 'name': 'Perpignan-Rivesaltes', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFRG', 'name': 'Deauville-Normandie', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFBI', 'name': 'Poitiers-Biard', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFSB', 'name': 'Bâle-Mulhouse', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFBL', 'name': 'Limoges-Bellegarde', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFCR', 'name': 'Rodez-Aveyron', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFJL', 'name': 'Metz-Nancy-Lorraine', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFMK', 'name': 'Carcassonne-Salvaza', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFOK', 'name': 'Châlons-Vatry', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFST', 'name': 'Strasbourg-Entzheim', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFMH', 'name': 'Saint-Étienne-Bouthéon', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFBU', 'name': 'Angoulême-Cognac', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFJY', 'name': 'CHAMBLEY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFOB', 'name': 'Beauvais-Tillé', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFAD', 'name': 'COMPIEGNE MARGNY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAF', 'name': 'LAON CHAMBRY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAJ', 'name': 'ARGENTAN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAP', 'name': 'RETHEL PERTHES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAQ', 'name': 'Albert-Bray', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFAR', 'name': 'MONTDIDIER', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAS', 'name': "FALAISE MONTS D'ERAINES", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAV', 'name': 'VALENCIENNES DENAIN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAW', 'name': 'VILLERUPT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAY', 'name': 'AMIENS-GLISY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFBK', 'name': 'Saint-Brieuc-Armor', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFBX', 'name': 'PERIGUEUX BASSILLAC', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCB', 'name': 'BAGNERES DE LUCHON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCC', 'name': 'Cahors-Lalbenque', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFCG', 'name': 'SAINT GIRONS ANTICHAN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCU', 'name': 'Avord', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFCV', 'name': 'VILLEFRANCHE DE ROUERGUE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDE', 'name': 'EGLETONS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDS', 'name': 'SARLAT DOMME', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDV', 'name': 'COUHE VERAC', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEG', 'name': 'ARGENTON SUR CREUSE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEI', 'name': 'BRIARE CHATILLON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEM', 'name': 'MONTARGIS VIMORY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEP', 'name': 'POUILLY MACONGE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFET', 'name': 'TIL CHATEL', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEU', 'name': 'BAR LE DUC LES HAUTS DE CHEE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEX', 'name': 'NANCY AZELOT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEZ', 'name': 'NANCY MALZEVILLE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFB', 'name': 'BUNO BONNEVAUX', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFG', 'name': 'LA FERTE GAUCHER', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFH', 'name': 'CHATEAU THIERRY BELLEAU', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFJ', 'name': 'JOINVILLE MUSSEY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFL', 'name': 'BAILLEAU ARMENONVILLE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFN', 'name': 'BRIENNE LE CHATEAU', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFP', 'name': 'PITHIVIERS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFR', 'name': 'BAR SUR SEINE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFT', 'name': 'NEUFCHATEAU', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFFZ', 'name': 'SEZANNE SAINT REMY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGA', 'name': 'Colmar-Houssen', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFGC', 'name': 'STRASBOURG NEUHOF', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGE', 'name': 'AVALLON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGK', 'name': 'JOIGNY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGN', 'name': 'PARAY LE MONIAL', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGP', 'name': 'SAINT FLORENTIN CHEU', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGQ', 'name': 'SEMUR EN AUXOIS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGR', 'name': 'DONCOURT LES CONFLANS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGS', 'name': 'LONGUYON VILLETTE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGT', 'name': 'SARREBOURG BUHL', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGU', 'name': 'SARREGUEMINES NEUNKIRCH', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGV', 'name': 'THIONVILLE YUTZ', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGW', 'name': 'VERDUN SOMMEDIEUE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGX', 'name': 'CHAMPAGNOLE CROTENAY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHA', 'name': 'ISSOIRE LE BROC', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHL', 'name': 'LANGOGNE LESPERON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHN', 'name': 'BELLEGARDE VOUVRAY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHP', 'name': 'Le Puy-Loudes', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFHR', 'name': 'BRIOUDE BEAUMONT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHS', 'name': 'BOURG CEYZERIAT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFID', 'name': 'CONDOM VALENCE SUR BAISE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFIF', 'name': 'SAINT AFFRIQUE BELMONT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFIG', 'name': 'CASSAGNES BEGONHES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFIK', 'name': 'RIBERAC SAINT AULAYE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFJC', 'name': 'CLAMECY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFJH', 'name': 'CAZERES PALAMINY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFJS', 'name': 'SOISSONS COURMELLES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFKM', 'name': 'SAINT GALMIER', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFLK', 'name': 'OYONNAX ARBENT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNO', 'name': 'FLORAC SAINTE ENIMIE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNQ', 'name': 'MONT LOUIS LA QUILLANE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNW', 'name': 'PUIVERT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNX', 'name': 'BEDARIEUX LA TOUR SUR ORB', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFOF', 'name': 'ALENCON VALFRAMBERT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFON', 'name': 'DREUX VERNOUILLET', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFOR', 'name': 'Chartres-Métropole', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFOS', 'name': 'SAINT VALERY VITTEFLEUR', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFOW', 'name': 'SAINT QUENTIN ROUPY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFOX', 'name': 'ETAMPES MONDESIR', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPA', 'name': 'PERSAN BEAUMONT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPE', 'name': 'MEAUX ESBLY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPK', 'name': 'COULOMMIERS VOISINS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPP', 'name': 'LE PLESSIS BELLEVILLE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQA', 'name': 'Reims-Prunay', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFQB', 'name': 'TROYES BARBEREY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQC', 'name': 'LUNEVILLE CROISMARE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQD', 'name': 'ARRAS ROCLINCOURT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQF', 'name': 'AUTUN BELLEVUE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQH', 'name': 'CHATILLON SUR SEINE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQJ', 'name': 'MAUBEUGE ELESMES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQK', 'name': 'CHALONS ECURY SUR COOLE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQL', 'name': 'LENS BENIFONTAINE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQS', 'name': 'VITRY EN ARTOIS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQU', 'name': 'SARRE UNION', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQW', 'name': 'VESOUL FROTEY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQX', 'name': 'JUVANCOURT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQY', 'name': 'SAVERNE STEINBOURG', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQZ', 'name': 'DIEUZE GUEBLANGE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFSE', 'name': 'EPINAL DOGNEVILLE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFSH', 'name': 'Haguenau', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFSJ', 'name': 'SEDAN DOUZY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFSK', 'name': 'Colmar-Houssen', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFSN', 'name': 'NANCY ESSEY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFSP', 'name': 'PONTARLIER', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFSU', 'name': 'LANGRES ROLAMPONT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFSV', 'name': 'PONT SAINT VINCENT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFSW', 'name': 'EPERNAY PLIVOT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFTP', 'name': 'PUIMOISSON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFXG', 'name': 'BITCHE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFXH', 'name': 'LE VALDAHON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFYG', 'name': 'CAMBRAI NIERGNIES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFYS', 'name': 'SAINTE LEOCADIE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFYV', 'name': 'YVETOT-BAONS LE COMTE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAG', 'name': 'PERONNE SAINT QUENTIN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAO', 'name': "BAGNOLES DE L'ORNE COUTERNE", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFAX', 'name': 'MORTAGNE AU PERCHE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFBA', 'name': 'Agen-La Garenne', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFBJ', 'name': 'SAINT JUNIEN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCE', 'name': 'GUERET SAINT LAURENT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCF', 'name': 'FIGEAC LIVERNON', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFCM', 'name': 'MILLAU LARZAC', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFDJ', 'name': 'PAMIERS LES PUJOLS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFEW', 'name': 'SAULIEU LIERNAIS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGM', 'name': 'MONTCEAU LES MINES POUILLOUX', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFGY', 'name': 'SAINT DIE REMOMEIX', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHQ', 'name': 'SAINT FLOUR COLTINES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHT', 'name': 'AMBERT LE POYET', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHZ', 'name': 'SALLANCHES MONT BLANC', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFIP', 'name': 'PEYRESOURDE BALESTAS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFJA', 'name': 'CHAUMONT SEMOUTIERS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFKA', 'name': 'ALBERTVILLE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFLA', 'name': 'Auxerre-Branches', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFLI', 'name': 'ANNEMASSE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFLT', 'name': 'MONTLUCON DOMERAT', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFLW', 'name': 'Aurillac', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFNB', 'name': 'MENDE BRENOUX', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFOC', 'name': 'Châteaudun', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFOG', 'name': 'FLERS SAINT PAUL', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFOJ', 'name': 'Orléans-Bricy', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFOL', 'name': "L'AIGLE SAINT MICHEL", 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFPC', 'name': 'Creil', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFQE', 'name': 'ETAIN ROUVRES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQI', 'name': 'CAMBRAI EPINOY', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQP', 'name': 'PHALSBOURG BOURSCHEID', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFQV', 'name': 'CHARLEVILLE MEZIERES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFSF', 'name': 'Metz-Nancy-Lorraine', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFSG', 'name': 'Épinal-Mirecourt', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFSI', 'name': 'Saint-Dizier-Robinson', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFSL', 'name': 'Brive-Vallée de la Dordogne', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFSO', 'name': 'Nancy-Ochey', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFSX', 'name': 'Montbéliard-Courcelles', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFSY', 'name': 'CESSEY BAIGNEUX LES JUIFS', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFTF', 'name': 'CUERS PIERREFEU', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFYD', 'name': 'Dinard', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFYM', 'name': 'MARIGNY LE GRAND', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFSR', 'name': 'Reims-Champagne', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFMD', 'name': 'Cannes-Mandelieu', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFMF', 'name': 'FAYENCE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFMC', 'name': 'Le Luc-Le Cannet', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFTZ', 'name': 'LA MOLE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFKC', 'name': 'Calvi-Sainte-Catherine', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFKG', 'name': 'GHISONACCIA ALZITONE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFKS', 'name': 'Solenzara', 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFKF', 'name': 'Figari-Sud-Corse', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFKJ', 'name': 'Ajaccio-Napoléon-Bonaparte', 'npf_type': 'pelicandrome_permanent'},
    {'oaci': 'LFMN', 'name': "Nice-Côte d'Azur", 'npf_type': 'aerodrome_selectionnable'},
    {'oaci': 'LFKD', 'name': 'SOLLIERES SARDIERES', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFKR', 'name': 'SAINT REMY DE MAURIENNE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFNC', 'name': 'MONT DAUPHIN SAINT CREPIN', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFHM', 'name': 'MEGEVE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFKO', 'name': 'PROPRIANO', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFKT', 'name': 'CORTE', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFKX', 'name': 'MERIBEL', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFLJ', 'name': 'COURCHEVEL', 'npf_type': 'aerodrome_carte'},
    {'oaci': 'LFMR', 'name': 'BARCELONNETTE SAINT PONS', 'npf_type': 'aerodrome_carte'}
]

TOTAL_AIRPORTS = len(NPF_AIRPORTS)
PELICANDROME_COUNT = sum(
    1 for a in NPF_AIRPORTS if a["npf_type"] == "pelicandrome_permanent"
)
SELECTABLE_AIRPORT_COUNT = sum(
    1 for a in NPF_AIRPORTS if a["npf_type"] == "aerodrome_selectionnable"
)
MAP_ONLY_AIRPORT_COUNT = sum(
    1 for a in NPF_AIRPORTS if a["npf_type"] == "aerodrome_carte"
)

if TOTAL_AIRPORTS != 446:
    raise RuntimeError(f"Périmètre NPF incohérent : {TOTAL_AIRPORTS} terrains au lieu de 446")
if len({a["oaci"] for a in NPF_AIRPORTS}) != TOTAL_AIRPORTS:
    raise RuntimeError("Codes OACI dupliqués dans NPF_AIRPORTS")

_thread_local = threading.local()


def get_session() -> requests.Session:
    s = getattr(_thread_local, "session", None)
    if s is None:
        s = requests.Session()
        s.headers.update(BASE_HEADERS)
        _thread_local.session = s
    return s


def clean_text(value: str) -> str:
    return " ".join((value or "").split())


def human_bytes(n: int | None) -> str:
    if n is None:
        return "inconnue"
    value = float(n)
    for unit in ("o", "Ko", "Mo", "Go"):
        if value < 1024 or unit == "Go":
            return f"{value:.1f} {unit}"
        value /= 1024
    return f"{n} o"


def target_label(icao: str) -> str:
    return f"AIP - AD-2.{icao}.pdf"


def search_url(icao: str, page: int = 1) -> str:
    return (
        f"{SIA}/catalogsearch/result/index/q/{icao}/"
        f"?c=8&format=pdf&page={page}&q={icao}"
    )


def extract_cycle(final_url: str) -> str:
    m = re.search(r"/eAIP_([^/]+)/", final_url or "", flags=re.I)
    return m.group(1) if m else ""


def load_existing_manifest(repo_root: Path) -> dict:
    p = repo_root / "manifest.json"
    if not p.exists():
        return {}
    try:
        data = json.loads(p.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def http_get_with_retry(url: str, **kwargs) -> requests.Response:
    s = get_session()
    for attempt in range(1, HTTP_ATTEMPTS + 1):
        try:
            r = s.get(url, **kwargs)
            if r.status_code >= 500 and attempt < HTTP_ATTEMPTS:
                r.close()
                time.sleep(2 * attempt)
                continue
            r.raise_for_status()
            return r
        except (requests.ConnectionError, requests.Timeout):
            if attempt == HTTP_ATTEMPTS:
                raise
            time.sleep(2 * attempt)
    raise RuntimeError(f"Échec HTTP après {HTTP_ATTEMPTS} tentatives : {url}")


def fetch_catalog_page(icao: str, page: int) -> dict:
    """Lit une page de l'onglet "Information aéronautique" et contrôle sa cohérence."""
    r = http_get_with_retry(
        search_url(icao, page),
        headers={**BASE_HEADERS, "Accept": "text/html,*/*;q=0.8"},
        timeout=(12, 35),
        allow_redirects=True,
    )
    soup = BeautifulSoup(r.text, "html.parser")

    tab_label = soup.find(id=f"tab-label-{RESULTS_TAB_ID}")
    tab = soup.find(id=RESULTS_TAB_ID)
    label_text = clean_text(tab_label.get_text(" ", strip=True)) if tab_label else ""
    if tab is None or not label_text.startswith(RESULTS_TAB_LABEL):
        raise RuntimeError(
            f"page {page} : onglet '{RESULTS_TAB_LABEL}' introuvable (structure SIA modifiée ?)"
        )

    docs = []
    for row in tab.select("tr.tr_ligne_document"):
        row_text = clean_text(row.get_text(" ", strip=True))
        links = [
            a for a in row.find_all("a", href=True)
            if "/documents/download/" in a["href"]
        ]
        if len(links) != 1:
            raise RuntimeError(f"page {page} : ligne de document inattendue : {row_text!r}")
        label = clean_text(links[0].get_text(" ", strip=True))
        category = row_text[len(label):].strip() if row_text.startswith(label) else row_text
        docs.append({
            "label": label,
            "category": category,
            "url": urljoin(r.url, links[0]["href"]),
        })

    amount = tab.select_one(".toolbar-amount")
    amount_text = clean_text(amount.get_text(" ", strip=True)) if amount else ""
    m_multi = re.fullmatch(r"Résultats (\d+) à (\d+) sur (\d+)", amount_text)
    m_single = re.fullmatch(r"(\d+) résultats?", amount_text)
    if m_multi:
        first, last, total = (int(x) for x in m_multi.groups())
    elif m_single:
        total = int(m_single.group(1))
        first, last = (1, total) if total else (0, 0)
    elif not amount and not docs and label_text == f"{RESULTS_TAB_LABEL} (0)":
        first, last, total = 0, 0, 0
    else:
        raise RuntimeError(
            f"page {page} : compteur de résultats illisible : {amount_text!r} / {label_text!r}"
        )

    if len(docs) != (last - first + 1 if total else 0):
        raise RuntimeError(
            f"page {page} : {len(docs)} documents lus pour l'intervalle {first}-{last}"
        )

    return {"page": page, "first": first, "last": last, "total": total, "docs": docs}


def resolve_exact_vac(airport: dict) -> dict:
    icao = airport["oaci"]
    expected_label = target_label(icao)

    result = {
        **airport,
        "expected_label": expected_label,
        "status": "error",
        "search_http": None,
        "stable_url": "",
        "resolve_error": "",
        "catalog_total": None,
        "catalog_pages_read": 0,
    }

    try:
        first_page = fetch_catalog_page(icao, 1)
        result["search_http"] = 200
        total = first_page["total"]
        result["catalog_total"] = total
        page_count = max(1, -(-total // RESULTS_PAGE_SIZE))
        if page_count > MAX_RESULT_PAGES:
            raise RuntimeError(f"{total} résultats : trop de pages ({page_count})")

        # La catégorie Atlas VAC est classée en fin de résultats : page 1 puis
        # de la dernière page vers la 2e, arrêt dès que la VAC est trouvée.
        docs_read = 0
        for page_no in [1] + list(range(page_count, 1, -1)):
            page = first_page if page_no == 1 else fetch_catalog_page(icao, page_no)
            result["catalog_pages_read"] += 1

            expected_first = (page_no - 1) * RESULTS_PAGE_SIZE + 1 if total else 0
            expected_last = min(page_no * RESULTS_PAGE_SIZE, total)
            if (page["total"], page["first"], page["last"]) != (
                total, expected_first, expected_last
            ):
                raise RuntimeError(
                    f"pagination incohérente page {page_no} : "
                    f"{page['first']}-{page['last']} sur {page['total']}, "
                    f"attendu {expected_first}-{expected_last} sur {total}"
                )
            docs_read += len(page["docs"])

            matches = {
                d["url"] for d in page["docs"]
                if d["label"] == expected_label and d["category"] == TARGET_CATEGORY
            }
            if len(matches) > 1:
                raise RuntimeError(
                    f"plusieurs documents '{expected_label}' en {TARGET_CATEGORY} : "
                    + ", ".join(sorted(matches))
                )
            if matches:
                result["stable_url"] = matches.pop()
                result["status"] = "found"
                return result

        if docs_read != total:
            raise RuntimeError(f"{docs_read} documents lus sur {total} annoncés")

        result["status"] = "no_vac"
        return result

    except Exception as exc:
        result["status"] = "error"
        result["resolve_error"] = f"{type(exc).__name__}: {exc}"
        return result


def get_current_cycle_from_sentinel() -> tuple[str, str, str]:
    sentinel = next(a for a in NPF_AIRPORTS if a["oaci"] == SENTINEL_ICAO)
    resolved = resolve_exact_vac(sentinel)
    if resolved["status"] != "found":
        raise RuntimeError(
            f"Impossible de résoudre la VAC témoin {SENTINEL_ICAO}: "
            f"{resolved.get('resolve_error') or resolved['status']}"
        )

    s = get_session()
    with s.get(
        resolved["stable_url"],
        headers={**BASE_HEADERS, "Accept": "application/pdf,*/*;q=0.8"},
        stream=True,
        allow_redirects=True,
        timeout=(12, 45),
    ) as r:
        r.raise_for_status()
        final_url = r.url
        cycle = extract_cycle(final_url)
        if not cycle:
            raise RuntimeError(
                f"Cycle SIA introuvable dans l'URL finale de {SENTINEL_ICAO}: {final_url}"
            )
        return cycle, resolved["stable_url"], final_url


def download_and_validate(resolved: dict, temp_dir: Path) -> dict:
    result = {
        **resolved,
        "pdf_http": None,
        "final_url": "",
        "content_type": "",
        "size_bytes": 0,
        "pdf_header_ok": False,
        "sha256": "",
        "sia_cycle": "",
        "download_error": "",
        "valid_pdf": False,
        "temp_path": "",
    }

    if resolved["status"] != "found":
        return result

    s = get_session()
    target = temp_dir / f"{resolved['oaci']}.pdf"

    try:
        sha = hashlib.sha256()
        total = 0
        first = True

        with s.get(
            resolved["stable_url"],
            headers={**BASE_HEADERS, "Accept": "application/pdf,*/*;q=0.8"},
            stream=True,
            allow_redirects=True,
            timeout=(12, 75),
        ) as r:
            result["pdf_http"] = r.status_code
            result["final_url"] = r.url
            result["content_type"] = r.headers.get("Content-Type", "")
            result["sia_cycle"] = extract_cycle(r.url)
            r.raise_for_status()

            with target.open("wb") as f:
                for chunk in r.iter_content(chunk_size=256 * 1024):
                    if not chunk:
                        continue
                    if first:
                        result["pdf_header_ok"] = chunk.startswith(b"%PDF-")
                        first = False
                    sha.update(chunk)
                    total += len(chunk)
                    f.write(chunk)

        result["size_bytes"] = total
        result["sha256"] = sha.hexdigest() if total else ""
        result["valid_pdf"] = (
            result["pdf_http"] == 200
            and result["pdf_header_ok"]
            and total > 0
            and "pdf" in result["content_type"].lower()
        )

        if not result["valid_pdf"]:
            if total == 0:
                result["download_error"] = "Fichier vide"
            elif not result["pdf_header_ok"]:
                result["download_error"] = "Le fichier ne commence pas par %PDF-"
            elif "pdf" not in result["content_type"].lower():
                result["download_error"] = (
                    f"Content-Type inattendu : {result['content_type']}"
                )
            target.unlink(missing_ok=True)
        else:
            result["temp_path"] = str(target)

    except Exception as exc:
        result["download_error"] = f"{type(exc).__name__}: {exc}"
        target.unlink(missing_ok=True)

    return result


def build_manifest(
    cycle: str,
    rows: list[dict],
    existing_manifest: dict,
    changed_files: list[str],
) -> dict:
    manifest_airports = {}
    total_size = 0
    available_count = 0

    for row in sorted(rows, key=lambda r: r["oaci"]):
        oaci = row["oaci"]
        base = {
            "name": row["name"],
            "npfType": row["npf_type"],
        }

        if row["status"] == "no_vac":
            base.update({
                "available": False,
                "status": "not_published_by_sia",
            })
            manifest_airports[oaci] = base
            continue

        if not row.get("valid_pdf"):
            raise RuntimeError(
                f"{oaci}: PDF non valide au moment de construire le manifeste"
            )

        file_rel = f"vac/{oaci}.pdf"
        base.update({
            "available": True,
            "status": "current",
            "file": file_rel,
            "size": int(row["size_bytes"]),
            "sha256": row["sha256"],
            "cycle": row.get("sia_cycle") or cycle,
            "source": "SIA",
            "sourceStableUrl": row["stable_url"],
            "sourceFinalUrl": row["final_url"],
        })
        manifest_airports[oaci] = base
        total_size += int(row["size_bytes"])
        available_count += 1

    return {
        "schemaVersion": 1,
        "source": "SIA / AIP Atlas VAC",
        "sourceCycle": cycle,
        "generatedAt": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "npfReference": "NPF-Q400 v16.50",
        "scope": {
            "pelicandromesPermanents": PELICANDROME_COUNT,
            "aerodromesSelectionnables": SELECTABLE_AIRPORT_COUNT,
            "aerodromesCarte": MAP_ONLY_AIRPORT_COUNT,
            "totalTerrains": TOTAL_AIRPORTS,
        },
        "stats": {
            "availableVac": available_count,
            "unavailableVac": TOTAL_AIRPORTS - available_count,
            "totalSizeBytes": total_size,
            "changedFilesThisSync": len(changed_files),
        },
        "airports": manifest_airports,
    }


def write_report(report_dir: Path, lines: list[str], payload: dict) -> None:
    report_dir.mkdir(parents=True, exist_ok=True)
    (report_dir / "summary.md").write_text(
        "\n".join(lines) + "\n",
        encoding="utf-8",
    )
    (report_dir / "sync_report.json").write_text(
        json.dumps(payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--force", action="store_true")
    parser.add_argument(
        "--accept-removals",
        action="store_true",
        help="Publier même si des VAC disponibles dans le manifeste ont disparu du SIA",
    )
    args = parser.parse_args()

    repo_root = Path(args.repo_root).resolve()
    vac_dir = repo_root / "vac"
    report_dir = repo_root / "sync-report"
    vac_dir.mkdir(parents=True, exist_ok=True)

    existing_manifest = load_existing_manifest(repo_root)
    existing_cycle = str(existing_manifest.get("sourceCycle") or "")
    existing_scope = existing_manifest.get("scope", {})
    existing_total = (
        int(existing_scope.get("totalTerrains") or 0)
        if isinstance(existing_scope, dict)
        else 0
    )
    scope_changed = existing_total != TOTAL_AIRPORTS

    started = time.monotonic()

    print("=== NPF-Q400-VAC — SYNCHRONISATION SIA ===")
    print(f"Dépôt : {repo_root}")
    print(f"Cycle enregistré : {existing_cycle or 'aucun'}")
    print(f"Périmètre : {TOTAL_AIRPORTS} terrains")
    print(f"Ancien périmètre : {existing_total or 'inconnu'}")
    print(f"Périmètre à reconstruire : {scope_changed}")
    print(f"Mode force : {args.force}")
    print(f"Retraits acceptés : {args.accept_removals}")

    try:
        current_cycle, sentinel_stable, sentinel_final = get_current_cycle_from_sentinel()
    except Exception as exc:
        lines = [
            "# Synchronisation VAC SIA",
            "",
            "❌ Impossible de déterminer le cycle SIA courant.",
            "",
            f"`{type(exc).__name__}: {exc}`",
        ]
        write_report(
            report_dir,
            lines,
            {"success": False, "stage": "cycle_detection", "error": str(exc)},
        )
        print(lines[-1])
        return 2

    print(f"Cycle SIA courant : {current_cycle}")

    if existing_cycle == current_cycle and not args.force and not scope_changed:
        elapsed = time.monotonic() - started
        lines = [
            "# Synchronisation VAC SIA",
            "",
            f"✅ Cycle SIA inchangé : **{current_cycle}**",
            "",
            f"Aucun téléchargement des {TOTAL_AIRPORTS} terrains n'a été nécessaire.",
            f"Durée : **{elapsed:.1f} s**",
        ]
        write_report(
            report_dir,
            lines,
            {
                "success": True,
                "changed": False,
                "sourceCycle": current_cycle,
                "reason": "same_cycle",
                "totalTerrains": TOTAL_AIRPORTS,
                "sentinelStableUrl": sentinel_stable,
                "sentinelFinalUrl": sentinel_final,
                "elapsedSeconds": round(elapsed, 2),
            },
        )
        print("Cycle et périmètre inchangés : aucune synchronisation complète.")
        return 0

    workers = max(1, min(int(args.workers), 6))
    reason = "force" if args.force else ("scope_changed" if scope_changed else "new_cycle")
    print(
        f"Synchronisation complète du cycle {current_cycle} "
        f"avec {workers} workers (raison={reason})."
    )

    resolved_rows = []
    technical_errors = []

    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {
            pool.submit(resolve_exact_vac, airport): airport
            for airport in NPF_AIRPORTS
        }
        for i, fut in enumerate(as_completed(futures), 1):
            row = fut.result()
            resolved_rows.append(row)
            print(
                f"[résolution {i:03d}/{TOTAL_AIRPORTS:03d}] "
                f"{row['oaci']} {row['status']}"
            )
            if row["status"] == "error":
                technical_errors.append(
                    f"{row['oaci']}: "
                    f"{row.get('resolve_error') or 'erreur de résolution'}"
                )

    if technical_errors:
        lines = [
            "# Synchronisation VAC SIA",
            "",
            "❌ Synchronisation annulée avant toute modification du dépôt.",
            "",
            "Erreurs de résolution du catalogue :",
            "",
        ] + [f"- {e}" for e in technical_errors]
        write_report(
            report_dir,
            lines,
            {
                "success": False,
                "stage": "catalog_resolution",
                "sourceCycle": current_cycle,
                "errors": technical_errors,
            },
        )
        return 3

    existing_airports = existing_manifest.get("airports", {})
    if not isinstance(existing_airports, dict):
        existing_airports = {}

    removed_rows = sorted(
        (
            r for r in resolved_rows
            if r["status"] == "no_vac"
            and isinstance(existing_airports.get(r["oaci"]), dict)
            and existing_airports[r["oaci"]].get("available") is True
        ),
        key=lambda r: r["oaci"],
    )
    removed_labels = [f"{r['oaci']} ({r['name']})" for r in removed_rows]
    if removed_rows:
        print(f"VAC disparues du site du SIA : {', '.join(removed_labels)}")

    if removed_rows and not args.accept_removals:
        lines = [
            f"❌ VAC disparue(s) sur le site du SIA : {', '.join(removed_labels)}. "
            "Rien n'a été publié. Vérifier puis relancer avec "
            "« accepter les retraits » coché.",
            "",
            "# Synchronisation VAC SIA",
            "",
            f"- Cycle SIA détecté : **{current_cycle}**",
            f"- Cycle publié conservé : **{existing_cycle or 'aucun'}**",
            f"- Terrains contrôlés : **{TOTAL_AIRPORTS}**",
            f"- VAC trouvées : **{sum(1 for r in resolved_rows if r['status'] == 'found')}**",
            f"- VAC disparues : **{len(removed_rows)}**",
            "",
            "## VAC disparues",
            "",
        ] + [f"- {label}" for label in removed_labels]
        write_report(
            report_dir,
            lines,
            {
                "success": False,
                "stage": "removed_vac",
                "sourceCycle": current_cycle,
                "publishedCycle": existing_cycle,
                "removedVac": [
                    {"oaci": r["oaci"], "name": r["name"]} for r in removed_rows
                ],
            },
        )
        print(lines[0])
        return 5

    found_rows = [r for r in resolved_rows if r["status"] == "found"]

    with tempfile.TemporaryDirectory(prefix="npf-vac-sync-") as tmp_name:
        temp_dir = Path(tmp_name)
        validated = {}
        download_errors = []

        with ThreadPoolExecutor(max_workers=workers) as pool:
            futures = {
                pool.submit(download_and_validate, row, temp_dir): row["oaci"]
                for row in found_rows
            }
            for i, fut in enumerate(as_completed(futures), 1):
                row = fut.result()
                validated[row["oaci"]] = row
                print(
                    f"[PDF {i:03d}/{len(found_rows):03d}] "
                    f"{row['oaci']} HTTP={row['pdf_http']} "
                    f"{human_bytes(row['size_bytes'])} valide={row['valid_pdf']}"
                )
                if not row["valid_pdf"]:
                    download_errors.append(
                        f"{row['oaci']}: "
                        f"{row.get('download_error') or 'PDF invalide'}"
                    )

        if download_errors:
            lines = [
                "# Synchronisation VAC SIA",
                "",
                "❌ Synchronisation annulée avant toute modification du dépôt.",
                "",
                "Erreurs de téléchargement/validation :",
                "",
            ] + [f"- {e}" for e in download_errors]
            write_report(
                report_dir,
                lines,
                {
                    "success": False,
                    "stage": "pdf_validation",
                    "sourceCycle": current_cycle,
                    "errors": download_errors,
                },
            )
            return 4

        rows = []
        for row in resolved_rows:
            if row["status"] == "found":
                rows.append(validated[row["oaci"]])
            else:
                rows.append(download_and_validate(row, temp_dir))

        changed_files = []
        unchanged_files = []

        # Toutes les validations sont terminées : seulement maintenant on modifie vac/.
        for row in rows:
            if not row.get("valid_pdf"):
                continue
            oaci = row["oaci"]
            old_sha = ""
            old_entry = existing_airports.get(oaci)
            if isinstance(old_entry, dict):
                old_sha = str(old_entry.get("sha256") or "")

            dest = vac_dir / f"{oaci}.pdf"
            if old_sha == row["sha256"] and dest.exists():
                unchanged_files.append(oaci)
                continue

            shutil.copy2(row["temp_path"], dest)
            changed_files.append(oaci)

        manifest = build_manifest(
            current_cycle,
            rows,
            existing_manifest,
            changed_files,
        )

        manifest_tmp = repo_root / "manifest.json.tmp"
        manifest_tmp.write_text(
            json.dumps(manifest, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
        manifest_tmp.replace(repo_root / "manifest.json")

    elapsed = time.monotonic() - started
    no_vac = sorted(r["oaci"] for r in rows if r["status"] == "no_vac")
    total_size = manifest["stats"]["totalSizeBytes"]

    lines = [
        "# Synchronisation VAC SIA",
        "",
        f"✅ Cycle synchronisé : **{current_cycle}**",
        "",
        f"- Terrains NPF : **{TOTAL_AIRPORTS}**",
        f"- Pélicandromes permanents : **{PELICANDROME_COUNT}**",
        f"- Aérodromes sélectionnables : **{SELECTABLE_AIRPORT_COUNT}**",
        f"- Autres aérodromes affichés : **{MAP_ONLY_AIRPORT_COUNT}**",
        f"- VAC disponibles : **{manifest['stats']['availableVac']}**",
        f"- Terrains sans VAC Atlas VAC : **{manifest['stats']['unavailableVac']}**",
        f"- Taille totale : **{human_bytes(total_size)}**",
        f"- PDF nouveaux ou modifiés : **{len(changed_files)}**",
        f"- PDF inchangés : **{len(unchanged_files)}**",
        f"- Durée : **{elapsed:.1f} s**",
        "",
        "## PDF nouveaux ou modifiés",
        "",
        ", ".join(changed_files) if changed_files else "Aucun.",
        "",
        "## Terrains sans VAC Atlas VAC",
        "",
        ", ".join(no_vac) if no_vac else "Aucun.",
        "",
        "## VAC retirées (retraits acceptés)",
        "",
        ", ".join(removed_labels) if removed_labels else "Aucune.",
    ]

    write_report(
        report_dir,
        lines,
        {
            "success": True,
            "changed": True,
            "reason": reason,
            "sourceCycle": current_cycle,
            "totalTerrains": TOTAL_AIRPORTS,
            "changedFiles": changed_files,
            "unchangedFiles": unchanged_files,
            "noVac": no_vac,
            "removedVac": [r["oaci"] for r in removed_rows],
            "availableVac": manifest["stats"]["availableVac"],
            "totalSizeBytes": total_size,
            "elapsedSeconds": round(elapsed, 2),
        },
    )

    print()
    print("=== TERMINÉ ===")
    print(f"Terrains contrôlés : {TOTAL_AIRPORTS}")
    print(f"VAC disponibles : {manifest['stats']['availableVac']}")
    print(f"PDF modifiés : {len(changed_files)}")
    print(f"Taille totale : {human_bytes(total_size)}")
    print(f"Durée : {elapsed:.1f} s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
