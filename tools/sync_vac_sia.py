#!/usr/bin/env python3
"""
Synchronisation SIA -> dépôt NPF-Q400-VAC.

Périmètre NPF TEST v14.92 :
- 27 pélicandromes permanents
- 96 aérodromes sélectionnables comme pélicandromes
- 123 codes OACI uniques

Sélection SIA stricte :
- libellé exact : AIP - AD-2.LFXX.pdf
- catégorie exacte : AIP Atlas VAC
- aucun SUP AIP ni autre document associé au terrain

Principes de sécurité :
- la synchronisation travaille d'abord en mémoire / fichiers temporaires ;
- le dépôt n'est modifié qu'après validation de tous les téléchargements nécessaires ;
- en cas d'erreur technique, le script échoue avant toute modification du manifeste ;
- une ancienne VAC déjà publiée n'est jamais supprimée automatiquement ;
- si une VAC n'est plus publiée par le SIA, le fichier historique peut rester sur GitHub
  mais le manifeste la marque indisponible afin que NPF ne l'affiche plus ;
- les mises à jour applicatives compareront les SHA-256.

Optimisation :
- un cycle témoin est résolu via LFBD ;
- si le cycle SIA est identique au cycle déjà enregistré dans manifest.json,
  le script sort sans recontrôler les 123 terrains, sauf --force ;
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

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/151 Safari/537.36 "
    "NPF-Q400-VAC-sync/1.0"
)

BASE_HEADERS = {
    "User-Agent": USER_AGENT,
    "Accept-Language": "fr-FR,fr;q=0.9,en;q=0.7",
    "Cache-Control": "no-cache",
}

NPF_AIRPORTS = [{'oaci': 'LFLU', 'name': 'Valence-Chabeuil', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFMU', 'name': 'Béziers-Vias', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFJR', 'name': 'Angers-Marcé', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFHO', 'name': 'Aubenas-Ardèche Méridionale', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFLX', 'name': 'Châteauroux-Déols', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFBM', 'name': 'Mont-de-Marsan', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFBL', 'name': 'Limoges-Bellegarde', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFAQ', 'name': 'Albert-Bray', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFBP', 'name': 'Pau-Pyrénées', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFTH', 'name': 'Toulon-Hyères', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFSG', 'name': 'Épinal-Mirecourt', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFKC', 'name': 'Calvi-Sainte-Catherine', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFMD', 'name': 'Cannes-Mandelieu', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFKB', 'name': 'Bastia-Poretta', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFMH', 'name': 'Saint-Étienne-Bouthéon', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFKF', 'name': 'Figari-Sud-Corse', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFCC', 'name': 'Cahors-Lalbenque', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFML', 'name': 'Marseille-Provence', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFKJ', 'name': 'Ajaccio-Napoléon-Bonaparte', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFMK', 'name': 'Carcassonne-Salvaza', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFRV', 'name': 'Vannes-Meucon', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFTW', 'name': 'Nîmes-Garons', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFMP', 'name': 'Perpignan-Rivesaltes', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFBD', 'name': 'Bordeaux-Mérignac', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFCR', 'name': 'Rodez-Aveyron', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFBN', 'name': 'Niort-Souché', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFSJ', 'name': 'Dole-Tavaux', 'npf_type': 'pelicandrome_permanent'}, {'oaci': 'LFBC', 'name': 'Cazaux', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFBH', 'name': 'La Rochelle-Île de Ré', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFBF', 'name': 'Toulouse-Francazal', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFBG', 'name': 'Cognac-Châteaubernard', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFBI', 'name': 'Poitiers-Biard', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFBK', 'name': 'Saint-Brieuc-Armor', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFBO', 'name': 'Toulouse-Blagnac', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFBS', 'name': 'Chambéry-Savoie', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFBT', 'name': 'Tarbes-Lourdes-Pyrénées', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFBU', 'name': 'Angoulême-Cognac', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFCU', 'name': 'Avord', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFLA', 'name': 'Auxerre-Branches', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFLC', 'name': 'Clermont-Ferrand-Auvergne', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFLD', 'name': 'Bourges', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFLL', 'name': 'Lyon-Saint Exupéry', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFLN', 'name': 'Saint-Yan', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFLS', 'name': 'Grenoble-Isère', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFLV', 'name': 'Vichy-Charmeil', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFLW', 'name': 'Aurillac', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFLY', 'name': 'Lyon-Bron', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFLZ', 'name': 'Le Puy-Loudes', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFMC', 'name': 'Le Luc-Le Cannet', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFMI', 'name': 'Istres-Le Tubé', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFMN', 'name': "Nice-Côte d'Azur", 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFMQ', 'name': 'Le Castellet', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFMV', 'name': 'Avignon-Provence', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFMY', 'name': 'Salon-de-Provence', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFOA', 'name': 'Avord', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFOC', 'name': 'Châteaudun', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFOE', 'name': 'Évreux-Fauville', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFOK', 'name': 'Châlons-Vatry', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFOJ', 'name': 'Orléans-Bricy', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFOP', 'name': 'Rouen-Vallée de Seine', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFOQ', 'name': 'Blois-Le Breuil', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFOR', 'name': 'Chartres-Métropole', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFOT', 'name': 'Tours-Val de Loire', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFOU', 'name': 'Cholet-Le Pontreau', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFOV', 'name': 'Laval-Entrammes', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFPB', 'name': 'Paris-Le Bourget', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFPC', 'name': 'Creil', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFPG', 'name': 'Paris-Charles-de-Gaulle', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFPO', 'name': 'Paris-Orly', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFPV', 'name': 'Villacoublay-Vélizy', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRB', 'name': 'Brest-Bretagne', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRC', 'name': 'Cherbourg-Manche', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRD', 'name': 'Dinard-Pleurtuit-Saint-Malo', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRE', 'name': 'La Baule-Escoublac', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRF', 'name': 'Granville-Mont-Saint-Michel', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRG', 'name': 'Deauville-Normandie', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRH', 'name': 'Lorient-Bretagne-Sud', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRI', 'name': 'La Roche-sur-Yon-Les Ajoncs', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRJ', 'name': 'Landivisiau', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRK', 'name': 'Caen-Carpiquet', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRL', 'name': 'Lanvéoc-Poulmic', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRM', 'name': 'Le Mans-Arnage', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRN', 'name': 'Rennes-Saint-Jacques', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRO', 'name': 'Lannion-Côte de Granit Rose', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRQ', 'name': 'Quimper-Pluguffan', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRS', 'name': 'Nantes-Atlantique', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRT', 'name': 'Saint-Nazaire-Montoir', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRU', 'name': 'Morlaix-Ploujean', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFSD', 'name': 'Dijon-Longvic', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFSF', 'name': 'Metz-Nancy-Lorraine', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFSH', 'name': 'Haguenau', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFSK', 'name': 'Colmar-Houssen', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFSO', 'name': 'Nancy-Ochey', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFSQ', 'name': 'Luxeuil-Saint-Sauveur', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFQA', 'name': 'Reims-Prunay', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFST', 'name': 'Strasbourg-Entzheim', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFSX', 'name': 'Montbéliard-Courcelles', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFYR', 'name': 'Romorantin-Pruniers', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFYD', 'name': 'Dinard', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFSR', 'name': 'Reims-Champagne', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFPM', 'name': 'Melun-Villaroche', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFOB', 'name': 'Beauvais-Tillé', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFQN', 'name': 'Saint-Omer-Wizernes', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFKS', 'name': 'Solenzara', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFBA', 'name': 'Agen-La Garenne', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFBE', 'name': 'Bergerac-Roumanière', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFDN', 'name': 'Rochefort-Saint-Agnant', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFBZ', 'name': 'Biarritz-Pays Basque', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFSL', 'name': 'Brive-Vallée de la Dordogne', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFJL', 'name': 'Metz-Nancy-Lorraine', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFSB', 'name': 'Bâle-Mulhouse', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFGA', 'name': 'Colmar-Houssen', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFSI', 'name': 'Saint-Dizier-Robinson', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFOH', 'name': 'Le Havre-Octeville', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFOI', 'name': 'Abbeville', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFMO', 'name': 'Orange-Caritat', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFLB', 'name': 'Chambéry-Savoie', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFLP', 'name': 'Annecy-Meythet', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFLO', 'name': 'Roanne-Renaison', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFHP', 'name': 'Le Puy-Loudes', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFMT', 'name': 'Montpellier-Méditerranée', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFQQ', 'name': 'Lille-Lesquin', 'npf_type': 'aerodrome_selectionnable'}, {'oaci': 'LFRZ', 'name': 'Saint-Nazaire-Montoir', 'npf_type': 'aerodrome_selectionnable'}]

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


def search_url(icao: str) -> str:
    return f"{SIA}/catalogsearch/result/?c=8&format=pdf&q={icao}"


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
    }

    s = get_session()
    try:
        r = s.get(
            search_url(icao),
            headers={**BASE_HEADERS, "Accept": "text/html,*/*;q=0.8"},
            timeout=(12, 35),
            allow_redirects=True,
        )
        result["search_http"] = r.status_code
        r.raise_for_status()

        soup = BeautifulSoup(r.text, "html.parser")
        rows = soup.select("tr.tr_ligne_document")
        if not rows:
            rows = soup.find_all("tr")

        for row in rows:
            row_text = clean_text(row.get_text(" ", strip=True))
            if TARGET_CATEGORY not in row_text:
                continue
            for link in row.find_all("a", href=True):
                label = clean_text(link.get_text(" ", strip=True))
                if label == expected_label:
                    result["stable_url"] = urljoin(r.url, link["href"])
                    result["status"] = "found"
                    return result

        result["status"] = "no_vac"
        return result

    except Exception as exc:
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
    existing_airports = existing_manifest.get("airports", {})
    if not isinstance(existing_airports, dict):
        existing_airports = {}

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
            # Le SIA ne publie actuellement aucune Atlas VAC exacte pour ce code.
            # On ne supprime pas physiquement une ancienne copie éventuelle,
            # mais elle n'est plus déclarée disponible dans le manifeste.
            base.update({
                "available": False,
                "status": "not_published_by_sia",
            })
            manifest_airports[oaci] = base
            continue

        if not row.get("valid_pdf"):
            raise RuntimeError(f"{oaci}: PDF non valide au moment de construire le manifeste")

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
        "npfReference": "TEST v14.92",
        "scope": {
            "pelicandromesPermanents": 27,
            "aerodromesSelectionnables": 96,
            "totalTerrains": 123,
        },
        "stats": {
            "availableVac": available_count,
            "unavailableVac": 123 - available_count,
            "totalSizeBytes": total_size,
            "changedFilesThisSync": len(changed_files),
        },
        "airports": manifest_airports,
    }


def write_report(report_dir: Path, lines: list[str], payload: dict) -> None:
    report_dir.mkdir(parents=True, exist_ok=True)
    (report_dir / "summary.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    (report_dir / "sync_report.json").write_text(
        json.dumps(payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()

    repo_root = Path(args.repo_root).resolve()
    vac_dir = repo_root / "vac"
    report_dir = repo_root / "sync-report"
    vac_dir.mkdir(parents=True, exist_ok=True)

    existing_manifest = load_existing_manifest(repo_root)
    existing_cycle = str(existing_manifest.get("sourceCycle") or "")

    started = time.monotonic()

    print("=== NPF-Q400-VAC — SYNCHRONISATION SIA ===")
    print(f"Dépôt : {repo_root}")
    print(f"Cycle enregistré : {existing_cycle or 'aucun'}")
    print(f"Mode force : {args.force}")

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

    if existing_cycle == current_cycle and not args.force:
        elapsed = time.monotonic() - started
        lines = [
            "# Synchronisation VAC SIA",
            "",
            f"✅ Cycle SIA inchangé : **{current_cycle}**",
            "",
            "Aucun téléchargement des 123 terrains n'a été nécessaire.",
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
                "sentinelStableUrl": sentinel_stable,
                "sentinelFinalUrl": sentinel_final,
                "elapsedSeconds": round(elapsed, 2),
            },
        )
        print("Cycle inchangé : aucune synchronisation complète.")
        return 0

    workers = max(1, min(int(args.workers), 6))
    print(f"Synchronisation complète du cycle {current_cycle} avec {workers} workers.")

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
            print(f"[résolution {i:03d}/123] {row['oaci']} {row['status']}")
            if row["status"] == "error":
                technical_errors.append(
                    f"{row['oaci']}: {row.get('resolve_error') or 'erreur de résolution'}"
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
                        f"{row['oaci']}: {row.get('download_error') or 'PDF invalide'}"
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

        existing_airports = existing_manifest.get("airports", {})
        if not isinstance(existing_airports, dict):
            existing_airports = {}

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

        manifest = build_manifest(current_cycle, rows, existing_manifest, changed_files)

        # Ecriture atomique du manifeste.
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
        f"- Terrains NPF : **123**",
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
    ]

    write_report(
        report_dir,
        lines,
        {
            "success": True,
            "changed": True,
            "sourceCycle": current_cycle,
            "changedFiles": changed_files,
            "unchangedFiles": unchanged_files,
            "noVac": no_vac,
            "availableVac": manifest["stats"]["availableVac"],
            "totalSizeBytes": total_size,
            "elapsedSeconds": round(elapsed, 2),
        },
    )

    print()
    print("=== TERMINÉ ===")
    print(f"VAC disponibles : {manifest['stats']['availableVac']}")
    print(f"PDF modifiés : {len(changed_files)}")
    print(f"Taille totale : {human_bytes(total_size)}")
    print(f"Durée : {elapsed:.1f} s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
