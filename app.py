"""
약결: 일반의약품 구매 전 성분 중복·주의사항 확인 보조 앱.

배포 대상: CPython 3.14 / Streamlit Community Cloud.
함께 제공된 requirements.txt를 반드시 같이 교체하세요.
Python 3.14 Linux wheel 의존성 다운로드 검증 완료; 실제 Cloud 실행은 별도 확인 필요.

실행:
    pip install -r requirements.txt
    streamlit run app.py

Streamlit Settings > Secrets 또는 환경변수:
    MFDS_SERVICE_KEY = "공공데이터포털 일반인증키"
    GOOGLE_VISION_API_KEY = "선택: Google Cloud Vision API 키"

공공데이터포털에서 다음 API 활용승인이 각각 필요합니다.
- 의약품 제품 허가정보 08
- DUR 품목정보 03
- e약은요

로그인과 영구 데이터베이스를 사용하지 않습니다.
프로필은 접속 세션의 서버 메모리에 보관합니다.

이 앱은 복용 가능 여부, 중단, 용량 변경을 결정하지 않습니다.
자료 없음은 안전하다는 의미가 아닙니다.
교육용 그래프는 실제 개인의 혈중농도를 예측하지 않습니다.

공식 API 명세 및 근거 검토일: 2026-11-13.
실제 승인키를 사용한 통합 검증은 별도로 필요합니다.
"""

import base64
import copy
import csv
import hashlib
import html
import io
import json
import math
import os
import re
import unicodedata
import urllib.parse
import uuid
import xml.etree.ElementTree as ET
from collections import defaultdict
from datetime import datetime, timezone, timedelta
from itertools import combinations
from pathlib import Path
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

import requests
import streamlit as st
from PIL import Image, ImageOps, UnidentifiedImageError


# ============================================================
# 기본 설정
# ============================================================

# tzdata is not bundled with every Python installation (notably Windows).
try:
    KST = ZoneInfo("Asia/Seoul")
except ZoneInfoNotFoundError:
    KST = timezone(timedelta(hours=9), name="KST")

APP_NAME = "약결"
APP_VERSION = "1.0.1"
REVIEW_DATE = "2026-11-13"

PERMIT_BASE = (
    "https://apis.data.go.kr/1471000/"
    "DrugPrdtPrmsnInfoService08/"
)
DUR_BASE = (
    "https://apis.data.go.kr/1471000/"
    "DURPrdlstInfoService03/"
)
EASY_BASE = (
    "https://apis.data.go.kr/1471000/"
    "DrbEasyDrugInfoService/"
)

MAX_API_BYTES = 12 * 1024 * 1024
API_PAGE_SIZE = 100
API_MAX_PAGES = 30

LEVELS = {
    "contraindication": ("⛔", "공식 병용금기", "#b42318"),
    "duplicate": ("◉", "동일 성분 중복", "#b54708"),
    "caution": ("!", "전문가 확인 필요", "#805500"),
    "unknown": ("?", "미확인 정보", "#475467"),
}

SCOPE_LABELS = {
    "official": "식약처 공식 자료",
    "general": "근거 기반 일반 주의 · 국내 DUR 판정 아님",
    "data": "성분·자료 점검",
}

SOURCES = {
    "mfds": "https://nedrug.mfds.go.kr/",
    "acetaminophen": (
        "https://www.fda.gov/drugs/"
        "safe-use-over-counter-pain-relievers-and-fever-reducers/"
        "acetaminophen"
    ),
    "nsaid": (
        "https://www.nhs.uk/medicines/ibuprofen-for-adults/"
    ),
    "kidney": (
        "https://www.niddk.nih.gov/health-information/"
        "kidney-disease/keeping-kidneys-safe"
    ),
    "hypo": (
        "https://www.niddk.nih.gov/health-information/diabetes/"
        "overview/preventing-problems/low-blood-glucose-hypoglycemia"
    ),
    "beta": (
        "https://www.cdc.gov/diabetes/about/"
        "low-blood-sugar-hypoglycemia.html"
    ),
    "cognition": (
        "https://www.nia.nih.gov/health/"
        "health-care-professionals-information/"
        "caring-older-patients-cognitive-impairment"
    ),
    "pseudo": (
        "https://www.nhs.uk/medicines/pseudoephedrine/"
    ),
    "anticholinergic": (
        "https://www.nhs.uk/medicines/"
        "chlorphenamine-including-piriton/"
        "who-can-and-cannot-take-chlorphenamine/"
    ),
    "asthma": (
        "https://sps.nhs.uk/articles/using-nsaids-in-asthma/"
    ),
    "heart": (
        "https://www.nice.org.uk/guidance/ng106/"
        "chapter/Recommendations"
    ),
    "arthritis": (
        "https://www.nice.org.uk/guidance/ng226/"
        "chapter/Recommendations"
    ),
    "warfarin": (
        "https://www.nhs.uk/medicines/anticoagulants/"
        "considerations/"
    ),
    "grapefruit": (
        "https://www.fda.gov/consumers/consumer-updates/"
        "grapefruit-juice-and-some-drugs-dont-mix"
    ),
    "thyroid": (
        "https://www.dailymed.nlm.nih.gov/dailymed/fda/"
        "fdaDrugXsl.cfm?"
        "setid=758588c3-c63e-491b-0aa2-4f50d80cb174&type=display"
    ),
    "renal_diet": (
        "https://www.niddk.nih.gov/health-information/"
        "kidney-disease/chronic-kidney-disease-ckd/"
        "healthy-eating-adults-chronic-kidney-disease"
    ),
    "insulin": (
        "https://sps.nhs.uk/articles/"
        "managing-the-risk-of-confusion-between-insulin-products/"
    ),
}

CAFFEINE_SOURCES = {
    "식약처 최대 일일섭취권고량": (
        "https://impfood.mfds.go.kr/CFBCC02F02/getCntntsDetail"
        "?cntntsMngId=00005&cntntsSn=278410"
    ),
    "FDA 성인 카페인 안내": (
        "https://www.fda.gov/consumers/consumer-updates/"
        "spilling-beans-how-much-caffeine-too-much"
    ),
    "CDC 반감기 교육자료": (
        "https://www.cdc.gov/niosh/"
        "work-hour-training-for-nurses/longhours/mod6/11.html"
    ),
    "MedlinePlus 테오필린": (
        "https://medlineplus.gov/druginfo/meds/a681006.html"
    ),
    "MedlinePlus 슈도에페드린": (
        "https://medlineplus.gov/druginfo/meds/a682619.html"
    ),
    "MedlinePlus 아미노필린": (
        "https://medlineplus.gov/druginfo/meds/a601015.html"
    ),
    "NCBI 카페인 약리 설명": (
        "https://www.ncbi.nlm.nih.gov/books/NBK223808/"
    ),
}

DISEASES = {
    "당뇨병": {
        "icon": "🩸",
        "short": "혈당·저혈당",
        "advice": (
            "인슐린·일부 혈당강하제는 결식·식사 지연·음주 때 "
            "저혈당 위험이 있습니다. 실제 복용약을 등록하세요. "
            "당뇨병 선택만으로 인슐린 복용을 추정하지 않습니다."
        ),
        "source": SOURCES["hypo"],
    },
    "고혈압": {
        "icon": "💓",
        "short": "혈압·코감기약",
        "advice": (
            "슈도에페드린 등 코막힘 성분과 진통소염제를 구매할 때 "
            "혈압 상태와 복용약을 약사에게 알려주세요."
        ),
        "source": SOURCES["pseudo"],
    },
    "골관절염·관절통": {
        "icon": "🦵",
        "short": "진통제 겹침",
        "advice": (
            "관절약·감기약·두통약의 진통 성분이 겹칠 수 있습니다. "
            "식품이나 보충제를 관절염 치료제 대신 사용하지 마세요."
        ),
        "source": SOURCES["arthritis"],
    },
    "인지저하·치매": {
        "icon": "🧠",
        "short": "졸림·혼동",
        "advice": (
            "일부 감기약·알레르기약·수면보조제의 항콜린성 성분은 "
            "졸림과 혼동을 유발할 수 있습니다. 전체 약 목록을 "
            "약사에게 보여주세요."
        ),
        "source": SOURCES["cognition"],
    },
    "만성콩팥병": {
        "icon": "💧",
        "short": "신장·식단 확인",
        "advice": (
            "진통소염제와 탈수, 건강기능식품에 주의가 필요합니다. "
            "칼륨·단백질·수분 제한은 검사와 병기에 따라 달라집니다."
        ),
        "source": SOURCES["renal_diet"],
    },
    "심부전": {
        "icon": "🫀",
        "short": "부종·체액",
        "advice": (
            "진통소염제는 체액 저류와 심부전 악화에 영향을 줄 수 "
            "있습니다. 새 일반약과 칼륨 함유 대체소금은 "
            "치료팀에 확인하세요."
        ),
        "source": SOURCES["heart"],
    },
    "위궤양·위장출혈 병력": {
        "icon": "🩹",
        "short": "출혈 위험",
        "advice": (
            "진통소염제와 항응고제·항혈소판제 조합은 별도 확인이 "
            "필요합니다. 궤양·출혈 병력을 알려주세요."
        ),
        "source": SOURCES["nsaid"],
    },
    "이상지질혈증": {
        "icon": "🫒",
        "short": "성분별 식품 주의",
        "advice": (
            "자몽 상호작용은 정확한 성분에 따라 다릅니다. "
            "모든 스타틴에 동일한 금기를 적용하지 않습니다."
        ),
        "source": SOURCES["grapefruit"],
    },
    "천식": {
        "icon": "🫁",
        "short": "진통제 반응 병력",
        "advice": (
            "아스피린·진통소염제로 숨참이나 천식 악화를 경험한 "
            "적이 있는지 확인하세요. 천식 전체를 절대금기로 "
            "판정하지 않습니다."
        ),
        "source": SOURCES["asthma"],
    },
    "녹내장·배뇨장애": {
        "icon": "👁️",
        "short": "감기약 성분 확인",
        "advice": (
            "일부 항히스타민·코막힘 성분은 폐쇄각녹내장·"
            "전립선비대 등에서 주의가 필요합니다. "
            "진단 유형과 증상을 알려주세요."
        ),
        "source": SOURCES["anticholinergic"],
    },
}


# ============================================================
# 화면 디자인
# ============================================================

CSS = """
<style>
@import url('https://fonts.googleapis.com/css2?family=Noto+Sans+KR:wght@400;500;600;700;800;900&display=swap');

:root {
    --ink:#102b3b;
    --muted:#5b7080;
    --mint:#0d766e;
    --line:#dce7ec;
}

html,body,.stApp {
    font-family:'Noto Sans KR',sans-serif;
}

.stApp {
    background:linear-gradient(145deg,#f0f7f7 0%,#f8fafc 48%,#f3f5fa 100%);
    color:var(--ink);
}

header[data-testid="stHeader"] {
    background:transparent;
    height:0;
}

[data-testid="stToolbar"] {
    display:none!important;
}

.block-container {
    max-width:990px;
    padding:1.1rem 1.2rem 1rem;
}

[data-testid="stVerticalBlock"] {
    gap:.55rem;
}

[data-testid="stCaptionContainer"] {
    color:#536775;
    font-size:.83rem;
}

.stButton button,
.stDownloadButton button,
.stFormSubmitButton button {
    border-radius:13px;
    min-height:46px;
    font-weight:700;
    border-color:#cddde4;
}

.stButton button[kind="primary"],
.stFormSubmitButton button[kind="primary"] {
    background:#0b746c;
    color:white;
    border-color:#0b746c;
}

.stButton button:hover,
.stDownloadButton button:hover {
    border-color:#0d766e;
    color:#0b665f;
}

.stTextInput input,
.stSelectbox [data-baseweb="select"] {
    font-size:1rem;
}

[data-testid="stMetric"] {
    background:#fff;
    border:1px solid var(--line);
    border-radius:14px;
    padding:10px 15px;
}

[data-testid="stMetricValue"] {
    font-size:1.45rem;
}

.brand {
    display:flex;
    align-items:center;
    gap:11px;
    margin:2px 0 6px;
}

.brand-icon {
    width:44px;
    height:44px;
    border-radius:15px;
    background:linear-gradient(140deg,#0c8178,#065b59);
    display:grid;
    place-items:center;
    box-shadow:0 6px 14px #086c6320;
}

.brand-title {
    font-size:23px;
    letter-spacing:-1.4px;
    font-weight:900;
    line-height:1.25;
}

.brand-sub {
    font-size:11px;
    letter-spacing:.12em;
    color:#50727e;
    font-weight:700;
}

.hero {
    position:relative;
    overflow:hidden;
    background:linear-gradient(125deg,#102f43,#123c4c 56%,#0b6863);
    border-radius:26px;
    padding:36px;
    color:white;
    box-shadow:0 15px 32px #12344518;
    margin:10px 0 18px;
}

.hero:after {
    content:'';
    position:absolute;
    width:260px;
    height:260px;
    border:45px solid #ffffff09;
    border-radius:50%;
    right:-78px;
    top:-40px;
    pointer-events:none;
}

.hero .eyebrow {
    font-size:12px;
    color:#9be7db;
    letter-spacing:.13em;
    font-weight:700;
}

.hero h1 {
    font-size:clamp(28px,4vw,42px);
    letter-spacing:-1.8px;
    line-height:1.35;
    margin:14px 0;
    font-weight:800;
    position:relative;
    z-index:1;
}

.hero p {
    font-size:16px;
    color:#e0efef;
    line-height:1.8;
    max-width:520px;
    margin:0;
    position:relative;
    z-index:1;
}

.hero-tag {
    display:inline-block;
    border:1px solid #95d7cb60;
    background:#ffffff0a;
    border-radius:20px;
    padding:6px 12px;
    font-size:12px;
    color:#d7ffef;
    margin-top:22px;
}

.intro-features {
    display:grid;
    grid-template-columns:repeat(3,1fr);
    gap:10px;
    margin-bottom:18px;
}

.intro-feature {
    background:white;
    border:1px solid var(--line);
    padding:18px 8px;
    border-radius:18px;
    text-align:center;
}

.intro-feature span {
    display:block;
    font-size:26px;
    margin-bottom:7px;
}

.intro-feature b {
    font-size:14px;
}

.intro-feature small {
    display:block;
    color:#546c77;
    font-size:12px;
    margin-top:5px;
}

.context {
    font-size:13px;
    color:#3e5f6b;
    padding:5px 0;
    line-height:1.7;
}

.pill {
    display:inline-block;
    border-radius:7px;
    background:#e6f2f0;
    color:#12625d;
    padding:2px 7px;
    margin:0 4px 3px 0;
    font-size:12px;
    font-weight:600;
}

.medline {
    background:white;
    border:1px solid var(--line);
    border-radius:14px;
    padding:11px 13px;
    margin:4px 0;
}

.medline small {
    color:#526975;
    font-size:12px;
}

.medline b {
    font-size:15px;
}

.empty {
    border:1px dashed #aec6cd;
    border-radius:14px;
    background:#ffffff80;
    padding:15px;
    color:#506d78;
    font-size:14px;
    text-align:center;
}

.resultrow {
    border-radius:13px;
    background:#fff;
    border:1px solid #dce7ec;
    padding:12px;
    margin-bottom:8px;
}

.resultrow .title {
    font-weight:800;
    font-size:15px;
    line-height:1.6;
}

.resultrow .detail {
    font-size:14px;
    color:#3d5460;
    line-height:1.75;
    margin-top:5px;
}

.resultrow .label {
    font-size:11px;
    font-weight:800;
}

.footer-note {
    font-size:12px;
    color:#546a76;
    text-align:center;
    line-height:1.7;
    margin:10px 0 0;
}

[data-testid="stDialog"] [role="dialog"] {
    border-radius:22px;
}

@media(max-width:600px) {
    .block-container {
        padding:.65rem .8rem .6rem;
    }
    [data-testid="stVerticalBlock"] {
        gap:.36rem;
    }
    [data-testid="stHorizontalBlock"] {
        gap:.4rem;
        flex-wrap:nowrap!important;
    }
    [data-testid="stColumn"] {
        min-width:0!important;
    }
    .hero {
        padding:26px 22px;
        border-radius:23px;
        margin:7px 0 12px;
    }
    .hero h1 {
        font-size:30px;
        margin:12px 0;
    }
    .hero p {
        font-size:14px;
        line-height:1.75;
    }
    .hero-tag {
        margin-top:16px;
        font-size:11px;
        padding:5px 9px;
    }
    .intro-features {
        gap:7px;
        margin-bottom:12px;
    }
    .intro-feature {
        padding:13px 4px;
    }
    .intro-feature b {
        font-size:12px;
    }
    .intro-feature small {
        font-size:10px;
    }
    .brand-title {
        font-size:21px;
    }
    .brand-icon {
        width:39px;
        height:39px;
        border-radius:13px;
    }
    .stButton button,
    .stDownloadButton button,
    .stFormSubmitButton button {
        min-height:46px;
        padding:.45rem .35rem;
        font-size:14px;
    }
    [data-testid="stMetric"] {
        padding:8px;
    }
    [data-testid="stMetricLabel"] p {
        font-size:11px;
    }
    [data-testid="stMetricValue"] {
        font-size:1.2rem;
    }
    .medline {
        padding:9px 11px;
    }
    .medline b {
        font-size:14px;
    }
}

@media(max-width:600px) and (max-height:740px) {
    .hero {
        padding:18px 20px;
    }
    .hero h1 {
        font-size:27px;
        margin:10px 0;
    }
    .hero p {
        font-size:13px;
        line-height:1.6;
    }
    .hero-tag {
        margin-top:12px;
    }
    .intro-feature {
        padding:9px 4px;
    }
    .intro-feature span {
        font-size:22px;
        margin-bottom:4px;
    }
    [data-testid="stMain"] [data-testid="stVerticalBlock"] {
        gap:.2rem;
    }
    .main-footer {
        display:none;
    }
}
</style>
"""

CAPSULE = """
<svg width="25" height="25" viewBox="0 0 32 32" aria-hidden="true">
<g transform="rotate(-40 16 16)">
<rect x="8" y="2" width="16" height="28" rx="8" fill="#fff"/>
<path d="M8 16h16v6a8 8 0 0 1-16 0z" fill="#7cddbb"/>
<path d="M8 16h16" stroke="#0d766e" stroke-width="1.4"/>
</g>
</svg>
"""


# ============================================================
# 공통 도구
# ============================================================

def h(value):
    return html.escape(str(value), quote=True)


def plain_text(value, limit=16000):
    value = re.sub(r"<[^>]+>", " ", str(value or ""))
    return value.replace("\x00", "")[:limit].strip()


def now_kst():
    return datetime.now(KST).strftime(
        "%Y-%m-%d %H:%M KST"
    )


def api_now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def text_value(value):
    if value is None:
        return ""
    if isinstance(value, dict):
        return str(value.get("#text", "")).strip()
    return str(value).strip()


def secret(name):
    try:
        return str(
            st.secrets.get(name, "") or os.environ.get(name, "")
        ).strip()
    except (FileNotFoundError, st.errors.StreamlitSecretNotFoundError):
        return os.environ.get(name, "").strip()


def api_key():
    return st.session_state.get("mfds_key", "") or secret(
        "MFDS_SERVICE_KEY"
    )


def vision_key():
    return st.session_state.get("vision_key", "") or secret(
        "GOOGLE_VISION_API_KEY"
    )


# ============================================================
# 식약처 공식 API
# ============================================================

class ApiError(Exception):
    """키와 요청 URL을 노출하지 않는 사용자용 오류."""


def xml_value(node):
    if not list(node):
        return node.text or ""

    result = {}

    for child in node:
        key = child.tag.rsplit("}", 1)[-1]
        value = xml_value(child)

        if key in result:
            if not isinstance(result[key], list):
                result[key] = [result[key]]
            result[key].append(value)
        else:
            result[key] = value

    return result


def check_result_code(code):
    if code in {"00", "000", "0"}:
        return

    if code in {
        "20", "30", "31", "21",
        "SERVICE_KEY_IS_NOT_REGISTERED_ERROR",
    }:
        raise ApiError(
            "API 키 또는 해당 서비스의 활용승인 상태를 확인해 주세요."
        )

    if code in {"22", "23"}:
        raise ApiError(
            "공식 API 호출 한도에 도달했습니다. 잠시 후 다시 확인해 주세요."
        )

    if code in {"03", "NODATA_ERROR"}:
        raise ApiError(
            "공식 API가 자료 없음 상태를 반환했습니다. "
            "조회 완료로 간주하지 않습니다."
        )

    raise ApiError(
        "공식 API 조회가 완료되지 않았습니다. "
        "설정과 서비스 상태를 확인해 주세요."
    )


def decode_api_response(raw):
    try:
        data = json.loads(raw.decode("utf-8-sig"))
    except (UnicodeError, ValueError):
        if b"<!DOCTYPE" in raw.upper() or b"<!ENTITY" in raw.upper():
            raise ApiError(
                "공식 API 응답 형식을 확인하지 못했습니다."
            ) from None

        try:
            data = xml_value(ET.fromstring(raw))
        except ET.ParseError:
            raise ApiError(
                "공식 API가 해석할 수 없는 응답을 반환했습니다."
            ) from None

    if not isinstance(data, dict):
        raise ApiError("공식 API 응답 형식을 확인하지 못했습니다.")

    if isinstance(data.get("response"), dict):
        data = data["response"]

    gateway = data.get("cmmMsgHeader")

    if isinstance(gateway, dict):
        check_result_code(text_value(gateway.get("returnReasonCode")))
        raise ApiError(
            "공식 API 게이트웨이에서 요청을 처리하지 못했습니다."
        )

    header = data.get("header")

    if not isinstance(header, dict):
        raise ApiError("공식 API의 결과 상태가 누락되었습니다.")

    check_result_code(text_value(header.get("resultCode")))

    body = data.get("body")

    if not isinstance(body, dict):
        raise ApiError("공식 API의 본문이 누락되었습니다.")

    try:
        total = int(body.get("totalCount"))
        if total < 0:
            raise ValueError
    except (ValueError, TypeError):
        raise ApiError(
            "공식 API의 전체 결과 수를 확인하지 못했습니다."
        ) from None

    items = body.get("items", [])

    if isinstance(items, dict):
        items = items.get("item", [])

    if items in (None, ""):
        items = []

    if isinstance(items, dict):
        items = [items]

    if (
        not isinstance(items, list)
        or any(not isinstance(row, dict) for row in items)
    ):
        raise ApiError("공식 API의 목록 형식이 예상과 다릅니다.")

    if total > 0 and not items:
        raise ApiError("공식 API 응답 목록이 누락되었습니다.")

    if total == 0 and items:
        raise ApiError(
            "공식 API의 전체 결과 수와 목록이 일치하지 않습니다."
        )

    return items, total


def api_get(
    base,
    operation,
    key,
    filters,
    page=1,
    rows=API_PAGE_SIZE,
):
    key = text_value(key)

    if not key:
        raise ApiError("공공데이터포털 API 키를 먼저 설정해 주세요.")

    if "%" in key:
        key = urllib.parse.unquote(key)

    params = {
        "serviceKey": key,
        "type": "json",
        "pageNo": page,
        "numOfRows": rows,
    }
    params.update(filters)

    try:
        with requests.get(
            base + operation,
            params=params,
            timeout=(4, 16),
            stream=True,
            allow_redirects=False,
        ) as response:
            if response.status_code in (401, 403):
                raise ApiError(
                    "API 키와 해당 서비스의 활용승인 여부를 확인해 주세요."
                )

            if response.status_code == 429:
                raise ApiError(
                    "공식 API 호출 한도에 도달했습니다."
                )

            if response.status_code != 200:
                raise ApiError(
                    "공식 API 서버에 연결하지 못했습니다."
                )

            chunks = []
            size = 0

            for chunk in response.iter_content(chunk_size=65536):
                size += len(chunk)

                if size > MAX_API_BYTES:
                    raise ApiError(
                        "공식 API 응답이 처리 한도를 초과했습니다."
                    )

                chunks.append(chunk)

            return decode_api_response(b"".join(chunks))

    except requests.RequestException:
        raise ApiError(
            "공식 API 연결이 지연되거나 실패했습니다. "
            "잠시 후 다시 확인해 주세요."
        ) from None


def api_all(
    base,
    operation,
    key,
    filters,
    max_pages=API_MAX_PAGES,
):
    rows = []
    expected = None
    seen_pages = set()

    for page in range(1, max_pages + 1):
        batch, total = api_get(
            base,
            operation,
            key,
            filters,
            page=page,
        )

        if expected is None:
            expected = total
        elif total != expected:
            raise ApiError(
                "조회 중 공식 자료 수가 변경되었습니다. 다시 점검해 주세요."
            )

        if total == 0:
            return []

        if not batch:
            raise ApiError(
                "공식 API 페이지가 누락되어 전체 조회를 완료하지 않았습니다."
            )

        fingerprint = json.dumps(
            batch,
            sort_keys=True,
            ensure_ascii=False,
        )

        if fingerprint in seen_pages:
            raise ApiError(
                "공식 API가 같은 페이지를 반복했습니다."
            )

        seen_pages.add(fingerprint)
        rows.extend(batch)

        if len(rows) >= total:
            if len(rows) != total:
                raise ApiError(
                    "공식 API 결과 수가 맞지 않습니다."
                )
            return rows

    raise ApiError(
        "공식 API 페이지 수가 처리 한도를 넘어 "
        "전체 조회를 완료하지 않았습니다."
    )


def item_url(item_seq):
    return (
        "https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq="
        + urllib.parse.quote(str(item_seq), safe="")
    )



# Offline education dataset: never silently equate a user upload to verified official data.
BUILTIN_OTC_ROWS = [{'ITEM_SEQ': '201507217', 'ITEM_NAME': '1. 포비딘인후스프레이액(포비돈요오드)(바닐라향), 2. 포비딘인후스프레이액(포비돈요오드)(청포도향)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '포비돈 요오드', 'ENTP_NAME': '(주)퍼슨', 'CHART': '제 1법 : 바닐라의 향과 감미 및 약간의 점성이 있는 옅은 갈색의 액제 제 2법 : 청포도의 향과 감미 및 약간의 점성이 있는 옅은 갈색의 액제', 'CHANGE_DATE': '2024-08-22', 'BAR_CODE': '8806574011006,8806574011013,8806574011020,8806574011037,8806574011044', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M215884]포비돈 요오드|[M215884]포비돈 요오드', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 포비돈 요오드|분량 : 0.45|단위 : 그램|규격 : USP|성분정보 : 유효요오드로서 45 mg;총량 : 100밀리리터|성분명 : 포비돈 요오드|분량 : 0.45|단위 : 그램|규격 : USP|성분정보 : 유효요오드로서 45 mg', '함량_총량기준': '100-제 1법/100-제 2법', '수집URL': 'https://drug.hospitalk.net/item/201507217', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201507217', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200511943', 'ITEM_NAME': '1.셀레나제100마이크로그램퍼오랄액(아셀렌산나트륨오수화물)2.셀레나제티퍼오랄액(아셀렌산나트륨오수화물)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아셀렌산나트륨오수화물', 'ENTP_NAME': '비오신코리아(주)', 'CHART': '흰색 플라스틱 용기에 든 무색 투명한 액제', 'CHANGE_DATE': '2015-01-06', 'BAR_CODE': '8806748000102,8806748000119,8806748000126,8806748000706,8806748000713,8806748000720', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M210377]아셀렌산나트륨오수화물|[M210377]아셀렌산나트륨오수화물', '함량_원료성분원문': '총량 : |성분명 : 아셀렌산나트륨오수화물|분량 : 0.332|단위 : 밀리그램|규격 : EP|성분정보 : 셀레늄으로서 100마이크로그램;총량 : |성분명 : 아셀렌산나트륨오수화물|분량 : 1.66|단위 : 밀리그램|규격 : EP|성분정보 : 셀레늄으로서 500마이크로그램', '함량_총량기준': '미기재', '수집URL': 'https://drug.hospitalk.net/item/200511943', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200511943', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201701571', 'ITEM_NAME': '1.셀레뉴원오랄액(아셀렌산나트륨오수화물) 2.셀큐민185오랄액(아셀렌산나트륨오수화물)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아셀렌산나트륨오수화물', 'ENTP_NAME': '(주)한국비엠아이', 'CHART': '1. 셀레뉴원오랄액 : 알루미늄포에 든 무색 투명한 액제 2. 셀큐민185오랄액 : 알루미늄포에 든 적황색의 액제', 'CHANGE_DATE': '2018-02-08', 'BAR_CODE': '8806548022908,8806548022915,8806548022922,8806548022939,8806548023707,8806548023714,8806548023721', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M210377]아셀렌산나트륨오수화물|[M210377]아셀렌산나트륨오수화물', '함량_원료성분원문': '총량 : 2mL 중|성분명 : 아셀렌산나트륨오수화물|분량 : 0.332|단위 : 밀리그램|규격 : EP|성분정보 : 셀레늄으로서 100mcg;총량 : 2mL 중|성분명 : 아셀렌산나트륨오수화물|분량 : 0.332|단위 : 밀리그램|규격 : EP|성분정보 : 셀레늄으로서 100mcg', '함량_총량기준': '2mL 중-1. 셀레뉴원오랄액(아셀렌산나트륨오수화물)/2mL 중-2. 셀큐민185오랄액(아셀렌산나트륨오수화물)', '수집URL': 'https://drug.hospitalk.net/item/201701571', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201701571', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005559', 'ITEM_NAME': '1.큐앤큐포비돈거즈볼-중(포비돈요오드)2.큐앤큐포비돈거즈볼-대(포비돈요오드)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '포비돈요오드', 'ENTP_NAME': '큐앤큐팜(주)', 'CHART': '어두운 적갈색 액을 흡착시킨 둥근 형태의 거즈', 'CHANGE_DATE': '2018-01-26', 'BAR_CODE': '8806810001402,8806810001419,8806810001426,8806810001433,8806810001440,8806810001457,8806810001464,8806810001471,8806810001488,8806810001495,8806810005707,8806810005714,8806810005721,8806810005738,8806810005745,8806810007008,8806810007015,8806810007022,8806810007039,8806810007046,8806810007053,8806810007107,8806810007114,8806810007121,8806810007138,8806810007145,8806810007152,8806810007404,8806810007411,8806810007428,8806810007435,8806810007442,8806810007459,8806810007503,8806810007510,8806810007527,8806810007534,8806810007541,8806810007558,8806810008203,8806810008210,8806810008227,8806810008234,8806810008241,8806810008302,8806810008319,8806810008326,8806810008333', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051757]포비돈요오드', '함량_원료성분원문': '총량 : 약 액 100㎖중 (거즈볼 1개 질량 : 1.중형11.08g(약액 9.74g 멸균거즈볼1.34g), 2.대형17.23g(약액 14.77g 멸균거즈볼2.46g))|성분명 : 포비돈요오드|분량 : 10.0|단위 : 그램|규격 : KP|성분정보 : 유효요오드로서 1.0g', '함량_총량기준': '약 액 100㎖중 (거즈볼 1개 질량 : 1.중형11.08g(약액 9.74g 멸균거즈볼1.34g), 2.대형17.23g(약액 14.77g 멸균거즈볼2.46g))-약 액 100ml 중/멸균거즈볼 1개(중형 1.34g) 중-흡착제1.중형/멸균거즈볼 1개(대형 2.46g) 중-흡착제2.대형', '수집URL': 'https://drug.hospitalk.net/item/200005559', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005559', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201507140', 'ITEM_NAME': '1.포리비돈인후스프레이(포비돈요오드)(바닐라향), 2.포리비돈인후스프레이(포비돈요오드)(청포도향)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '포비돈요오드', 'ENTP_NAME': '태극제약(주)', 'CHART': '제 1법 : 바닐라의 향과 감미 및 약간의 점성이 있는 옅은 갈색의 액제 제 2법 : 청포도의 향과 감미 및 약간의 점성이 있는 옅은 갈색의 액제', 'CHANGE_DATE': '2025-08-13', 'BAR_CODE': '8806448053200,8806448053217', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M244708]포비돈요오드|[M244708]포비돈요오드', '함량_원료성분원문': '총량 : 이 약 100밀리리터 중|성분명 : 포비돈요오드|분량 : 0.45|단위 : 그램|규격 : USP|성분정보 : 유효요오드(으)로서 45 밀리그램;총량 : 이 약 100밀리리터 중|성분명 : 포비돈요오드|분량 : 0.45|단위 : 그램|규격 : USP|성분정보 : 유효요오드(으)로서 45 밀리그램', '함량_총량기준': '이 약 100밀리리터 중-[제1법]/이 약 100밀리리터 중-[제2법]', '수집URL': 'https://drug.hospitalk.net/item/201507140', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201507140', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201904494', 'ITEM_NAME': '5-엠씨크림(리도카인)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '리도카인', 'ENTP_NAME': '주식회사더유제약', 'CHART': '흰색 또는 연노랑의 크림제', 'CHANGE_DATE': '2024-06-05', 'BAR_CODE': '8800570000200,8800570000217,8800570000224,8800570000231', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040131]리도카인', '함량_원료성분원문': '총량 : 1그램|성분명 : 리도카인|분량 : 96.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/201904494', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201904494', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201802476', 'ITEM_NAME': '가그린목액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '벤지다민염산염;세틸피리디늄염화물수화물', 'ENTP_NAME': '동아제약(주)', 'CHART': '이 약은 무색~미황색의 액제이다.', 'CHANGE_DATE': '2022-10-06', 'BAR_CODE': '8806265018109,8806265018116,8806265018123', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M222851]벤지다민염산염|[M250372]세틸피리디늄염화물수화물', '함량_원료성분원문': '총량 : 이 약 100mL 중|성분명 : 벤지다민염산염|분량 : 150|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 100mL 중|성분명 : 세틸피리디늄염화물수화물|분량 : 50|단위 : 밀리그램|규격 : EP|성분정보 :', '함량_총량기준': '이 약 100mL 중', '수집URL': 'https://drug.hospitalk.net/item/201802476', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201802476', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201804312', 'ITEM_NAME': '가네리버연질캡슐175mg(밀크시슬열매건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '밀크시슬열매건조엑스', 'ENTP_NAME': '한국휴텍스제약(주)', 'CHART': '갈색의 액상 내용물이 든 투명한 갈색의 장방형 연질캡슐', 'CHANGE_DATE': '2019-03-22', 'BAR_CODE': '8806491041100,8806491041117', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268656]밀크시슬열매건조엑스', '함량_원료성분원문': '총량 : 1캡슐(1,660mg) 중 |성분명 : 밀크시슬열매건조엑스|분량 : 175.0|단위 : 밀리그램|규격 : 생규|성분정보 : 실리마린으로서 98밀리그램', '함량_총량기준': '1캡슐(1,660mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201804312', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201804312', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201801343', 'ITEM_NAME': '가네리버연질캡슐350mg(밀크시슬열매건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '밀크시슬열매건조엑스', 'ENTP_NAME': '한국휴텍스제약(주)', 'CHART': '황갈색의 유상 내용물을 함유한 녹색의 장방형 연질캡슐제', 'CHANGE_DATE': '2019-03-22', 'BAR_CODE': '8806491038803,8806491038810,8806491038827', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268656]밀크시슬열매건조엑스', '함량_원료성분원문': '총량 : 1캡슐(1,135mg) 중|성분명 : 밀크시슬열매건조엑스|분량 : 350.0|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1캡슐(1,135mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201801343', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201801343', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201700282', 'ITEM_NAME': '가네맥스연질캡슐(밀크시슬열매건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '밀크시슬열매건조엑스', 'ENTP_NAME': '코스맥스파마(주)', 'CHART': '황갈색의 유상 내용물을 함유한 암적색의 장방형 연질캡슐', 'CHANGE_DATE': '2025-01-20', 'BAR_CODE': '8800540002401,8800540002418,8800540002425,8800551021903,8800551021910,8800551021927', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268656]밀크시슬열매건조엑스', '함량_원료성분원문': '총량 : 1캡슐1,240밀리그램|성분명 : 밀크시슬열매건조엑스|분량 : 350.00|단위 : 밀리그램|규격 : 생규|성분정보 : 실리마린으로서 196mg', '함량_총량기준': '11,240', '수집URL': 'https://drug.hospitalk.net/item/201700282', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201700282', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202201483', 'ITEM_NAME': '가네원연질캡슐350밀리그램(밀크시슬열매건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '밀크시슬열매건조엑스', 'ENTP_NAME': '대원제약(주)', 'CHART': '황갈색의 유상 내용물을 함유한 암적색(검붉은 색)의 타원형 연질캡슐', 'CHANGE_DATE': '2022-04-22', 'BAR_CODE': '8806718075000,8806718075017,8806718075024', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268656]밀크시슬열매건조엑스', '함량_원료성분원문': '총량 : 1캡슐1110밀리그램|성분명 : 밀크시슬열매건조엑스|분량 : 350.00|단위 : 밀리그램|규격 : 생규|성분정보 : 실리마린(으)로서 196 밀리그램', '함량_총량기준': '11110', '수집URL': 'https://drug.hospitalk.net/item/202201483', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202201483', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201304386', 'ITEM_NAME': '가네조아350연질캡슐(밀크시슬열매건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '밀크시슬열매건조엑스', 'ENTP_NAME': '위더스제약(주)', 'CHART': '황갈색의 유상 내용물을 함유한 암적색의 장방형 연질캡슐', 'CHANGE_DATE': '2024-12-09', 'BAR_CODE': '8806607025307,8806607025314,8806607025321,8806607025338', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268656]밀크시슬열매건조엑스', '함량_원료성분원문': '총량 : 1캡슐1,240밀리그램|성분명 : 밀크시슬열매건조엑스|분량 : 350.00|단위 : 밀리그램|규격 : 생규|성분정보 : 실리마린으로서 196mg', '함량_총량기준': '11,240', '수집URL': 'https://drug.hospitalk.net/item/201304386', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201304386', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201804162', 'ITEM_NAME': '가네존연질캡슐(밀크시슬열매건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '밀크시슬열매건조엑스', 'ENTP_NAME': '(주)이든파마', 'CHART': '황갈색의 유상 내용물을 함유한 암적색의 장방형 연질캡슐', 'CHANGE_DATE': '2025-11-26', 'BAR_CODE': '8806289011308,8806289011315,8806289011322,8806289011339,8806289011346,8806289011353,8806289011360', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268656]밀크시슬열매건조엑스', '함량_원료성분원문': '총량 : 1캡슐1240밀리그램|성분명 : 밀크시슬열매건조엑스|분량 : 350.00|단위 : 밀리그램|규격 : 생규|성분정보 : 실리마린으로서 196mg', '함량_총량기준': '11240', '수집URL': 'https://drug.hospitalk.net/item/201804162', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201804162', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202601036', 'ITEM_NAME': '가네존정175밀리그램(밀크시슬열매건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '밀크시슬열매건조엑스', 'ENTP_NAME': '(주)이든파마', 'CHART': '적갈색의 장방형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '미기재', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268656]밀크시슬열매건조엑스', '함량_원료성분원문': '총량 : 1정470밀리그램|성분명 : 밀크시슬열매건조엑스|분량 : 175|단위 : 밀리그램|규격 : 생규|성분정보 : 실리마린(으)로서 96.25 밀리그램', '함량_총량기준': '1470', '수집URL': 'https://drug.hospitalk.net/item/202601036', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202601036', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202601035', 'ITEM_NAME': '가네존정350밀리그램(밀크시슬열매건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '밀크시슬열매건조엑스', 'ENTP_NAME': '(주)이든파마', 'CHART': '적갈색의 장방형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '미기재', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268656]밀크시슬열매건조엑스', '함량_원료성분원문': '총량 : 1정940밀리그램|성분명 : 밀크시슬열매건조엑스|분량 : 350|단위 : 밀리그램|규격 : 생규|성분정보 : 실리마린(으)로서 192.5 밀리그램', '함량_총량기준': '1940', '수집URL': 'https://drug.hospitalk.net/item/202601035', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202601035', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201600574', 'ITEM_NAME': '가네진정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시아노코발라민100배산;리보플라빈;피리독신염산염;아데닌염산염;항독성간장엑스;오로트산카르니틴', 'ENTP_NAME': '(주)셀트리온제약', 'CHART': '적갈색의 타원형 필름코팅정제', 'CHANGE_DATE': '2019-05-13', 'BAR_CODE': '8806939020605,8806939020612,8806939020629,8806939020636,8806939020643,8806939020650', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256157]시아노코발라민100배산|[M040133]리보플라빈|[M204304]피리독신염산염|[M253171]아데닌염산염|[M081379]항독성간장엑스|[M081378]오로트산카르니틴', '함량_원료성분원문': '총량 : 이 약 1정(805.0mg) 중|성분명 : 오로트산카르니틴|분량 : 300|단위 : 밀리그램|규격 : 별규|성분정보 : 오로트산으로서147.6mg, 카르니틴으로서 152.4mg;총량 : 이 약 1정(805.0mg) 중|성분명 : 항독성간장엑스|분량 : 25|단위 : 밀리그램|규격 : 별규|성분정보 : 시아노코발라민으로서 0.25㎍;총량 : 이 약 1정(805.0mg) 중|성분명 : 아데닌염산염|분량 : 5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 이 약 1정(805.0mg) 중|성분명 : 피리독신염산염|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1정(805.0mg) 중|성분명 : 리보플라빈|분량 : 1|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1정(805.0mg) 중|성분명 : 시아노코발라민100배산|분량 : 25|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '이 약 1정(805.0mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201600574', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201600574', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202005641', 'ITEM_NAME': '가네치온정100밀리그램(글루타티온(환원형))', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '글루타티온(환원형)', 'ENTP_NAME': '주식회사더유제약', 'CHART': '흰색의 원형 필름코팅정이다.', 'CHANGE_DATE': '2025-04-02', 'BAR_CODE': '8800570014504,8800570014511', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256276]글루타티온(환원형)', '함량_원료성분원문': '총량 : 1정235.4밀리그램|성분명 : 글루타티온(환원형)|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1235.4', '수집URL': 'https://drug.hospitalk.net/item/202005641', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202005641', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198601398', 'ITEM_NAME': '가네카정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '트리프롤리딘염산염수화물;슈도에페드린염산염', 'ENTP_NAME': '지엘팜텍(주)', 'CHART': '백색의 원형 정제.', 'CHANGE_DATE': '2025-06-26', 'BAR_CODE': '8806242006204,8806242006211,8806497000101,8806497000118,8806497000125,8806497000132,8806497000149,8806497000156,8806497000163,8806497000170,8806497000187,8806497000194,8806497018212', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M250460]트리프롤리딘염산염수화물|[M203364]슈도에페드린염산염', '함량_원료성분원문': '총량 : 1정(140mg)중|성분명 : 트리프롤리딘염산염수화물|분량 : 2.5|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1정(140mg)중|성분명 : 슈도에페드린염산염|분량 : 60|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1정(140mg)중-국내용', '수집URL': 'https://drug.hospitalk.net/item/198601398', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198601398', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201700839', 'ITEM_NAME': '가네타인액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': 'L-아르기닌;베타인;베타인염산염;시트르산수화물', 'ENTP_NAME': '동성제약(주)', 'CHART': '갈색의 불투명한 플라스틱 바이알에 든 엷은 담갈색의 액제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806432029303,8806432029310,8806432029327,8806432029334', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M103077]L-아르기닌|[M050571]베타인|[M241790]베타인염산염|[M223090]시트르산수화물', '함량_원료성분원문': '총량 : 100mL 중|성분명 : L-아르기닌|분량 : 7.31|단위 : 그램|규격 : USP|성분정보 : ;총량 : 100mL 중|성분명 : 베타인|분량 : 5.00|단위 : 그램|규격 : 별규|성분정보 : ;총량 : 100mL 중|성분명 : 베타인염산염|분량 : 5.00|단위 : 그램|규격 : USP|성분정보 : 베타인으로서3.8135g;총량 : 100mL 중|성분명 : 시트르산수화물|분량 : 2.94|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '100mL 중', '수집URL': 'https://drug.hospitalk.net/item/201700839', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201700839', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202602422', 'ITEM_NAME': '가네타치온정(글루타티온(환원형))', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '글루타티온(환원형)', 'ENTP_NAME': '제이더블유중외제약(주)', 'CHART': '흰색의 원형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806449156603,8806449156610,8806449156627,8806449156634', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256276]글루타티온(환원형)', '함량_원료성분원문': '총량 : 1정301밀리그램|성분명 : 글루타티온(환원형)|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1301', '수집URL': 'https://drug.hospitalk.net/item/202602422', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202602422', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200808096', 'ITEM_NAME': '가네탑골드연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시아노코발라민;판토텐산 칼슘;니코틴산아미드;피리독신염산염;티아민질산염;밀크시슬열매건조엑스', 'ENTP_NAME': '일양약품(주)', 'CHART': '황갈색의 내용물을 함유하는 암갈색의 장방형 연질캡슐제', 'CHANGE_DATE': '2020-01-22', 'BAR_CODE': '8806417045205,8806417045212,8806431032502', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M096429]시아노코발라민|[M243177]판토텐산 칼슘|[M040064]니코틴산아미드|[M204304]피리독신염산염|[M223262]티아민질산염|[M268656]밀크시슬열매건조엑스', '함량_원료성분원문': '총량 : 이 약 1캡슐(1,177밀리그램)중|성분명 : 밀크시슬열매건조엑스|분량 : 200|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 이 약 1캡슐(1,177밀리그램)중|성분명 : 티아민질산염|분량 : 4|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1캡슐(1,177밀리그램)중|성분명 : 피리독신염산염|분량 : 4|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1캡슐(1,177밀리그램)중|성분명 : 니코틴산아미드|분량 : 12|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1캡슐(1,177밀리그램)중|성분명 : 판토텐산 칼슘|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1캡슐(1,177밀리그램)중|성분명 : 시아노코발라민|분량 : 1.2|단위 : 마이크로그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 1캡슐(1,177밀리그램)중', '수집URL': 'https://drug.hospitalk.net/item/200808096', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200808096', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200810915', 'ITEM_NAME': '가네탑플러스연질캡슐350밀리그램(밀크시슬열매건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '밀크시슬열매건조엑스', 'ENTP_NAME': '일양약품(주)', 'CHART': '황갈색의 유상 내용물을 함유한 암적색(검붉은 색)의 장방형 연질캡슐', 'CHANGE_DATE': '2020-04-20', 'BAR_CODE': '8806417028109,8806417028116', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268656]밀크시슬열매건조엑스', '함량_원료성분원문': '총량 : 이 약 (1,140밀리그램) 중|성분명 : 밀크시슬열매건조엑스|분량 : 350.00|단위 : 밀리그램|규격 : 생규|성분정보 : 실리마린으로서 196밀리그램', '함량_총량기준': '이 약 (1,140밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200810915', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200810915', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202102087', 'ITEM_NAME': '가네톡액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시트르산수화물;베타인염산염;베타인;L-아르기닌', 'ENTP_NAME': '제이더블유중외제약(주)', 'CHART': '스틱파우치에 든 엷은 담갈색의 내용 액제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806449149100,8806449149117,8806449149124,8806449149131,8806449149148', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223090]시트르산수화물|[M241790]베타인염산염|[M050571]베타인|[M103077]L-아르기닌', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : L-아르기닌|분량 : 7.31|단위 : 그램|규격 : EP|성분정보 : ;총량 : 100밀리리터|성분명 : 베타인|분량 : 5.00|단위 : 그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 100밀리리터|성분명 : 베타인염산염|분량 : 5.00|단위 : 그램|규격 : USP|성분정보 : 베타인(으)로서 3.8135 그램;총량 : 100밀리리터|성분명 : 시트르산수화물|분량 : 2.94|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/202102087', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202102087', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202303237', 'ITEM_NAME': '가넥트액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '베타인염산염;우르소데옥시콜산;니코틴산아미드;피리독신염산염;리보플라빈포스페이트나트륨;벤포티아민', 'ENTP_NAME': '동아제약(주)', 'CHART': '갈색 유리병에 든 황색의 투명한 액제', 'CHANGE_DATE': '2024-01-17', 'BAR_CODE': '8806265019502,8806265019519', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M241790]베타인염산염|[M223167]우르소데옥시콜산|[M040064]니코틴산아미드|[M204304]피리독신염산염|[M222996]리보플라빈포스페이트나트륨|[M096428]벤포티아민', '함량_원료성분원문': '총량 : 1병100밀리리터|성분명 : 벤포티아민|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : 티아민염산염(으)로서 36.2 밀리그램;총량 : 1병100밀리리터|성분명 : 리보플라빈포스페이트나트륨|분량 : 12|단위 : 밀리그램|규격 : KP|성분정보 : 리보플라빈(으)로서 9.4 밀리그램;총량 : 1병100밀리리터|성분명 : 피리독신염산염|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 니코틴산아미드|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 우르소데옥시콜산|분량 : 60|단위 : 밀리그램|규격 : EP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 베타인염산염|분량 : 20|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1100', '수집URL': 'https://drug.hospitalk.net/item/202303237', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202303237', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199902902', 'ITEM_NAME': '가레오액(디히드록시디부틸에테르)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '디히드록시디부틸에테르', 'ENTP_NAME': '조아제약(주)', 'CHART': '무색의 투명한 액체가 들어있는 앰플·병·플라스틱 및 포 용기', 'CHANGE_DATE': '2025-03-10', 'BAR_CODE': '8806446000206,8806446000213,8806446000220,8806446000237,8806446000244,8806446000251,8806446000268,8806446000275,8806446000282,8806446000299,8806446037219,8806446037226', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256801]디히드록시디부틸에테르|[M256801]디히드록시디부틸에테르', '함량_원료성분원문': '총량 : 이 약 100 mL 중|성분명 : 디히드록시디부틸에테르|분량 : 10|단위 : 그램|규격 : KP|성분정보 : ;총량 : 이 약 100 mL 중|성분명 : 디히드록시디부틸에테르|분량 : 10|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 100 mL 중-(앰플,포)/이 약 100 mL 중-(병, 플라스틱 용기)', '수집URL': 'https://drug.hospitalk.net/item/199902902', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199902902', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198802329', 'ITEM_NAME': '가레오연질캡슐(디히드록시디부틸에테르)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '디히드록시디부틸에테르', 'ENTP_NAME': '조아제약(주)', 'CHART': '일면유백색, 일면흑색의 타원형 연질캅셀제', 'CHANGE_DATE': '2025-08-04', 'BAR_CODE': '8806446000305,8806446000312,8806446000329,8806446000336', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256801]디히드록시디부틸에테르', '함량_원료성분원문': '총량 : 1캡슐(688mg) 중|성분명 : 디히드록시디부틸에테르|분량 : 250|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1캡슐(688mg) 중', '수집URL': 'https://drug.hospitalk.net/item/198802329', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198802329', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198802326', 'ITEM_NAME': '가레오연질캡슐500밀리그램(디히드록시디부틸에테르)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '디히드록시디부틸에테르', 'ENTP_NAME': '조아제약(주)', 'CHART': '<내수용, 수출용1>투명한 액상의 내용물이 든 일면 유백색,일면 흑색의 장방형의 연질캡슐제 <수출용2>투명한 액상의 내용물이 든 무색 투명한 장방형 연질캡슐제', 'CHANGE_DATE': '2025-08-04', 'BAR_CODE': '8806446000404,8806446000411,8806446000428,8806446000435,8806446000442', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256801]디히드록시디부틸에테르|[M256801]디히드록시디부틸에테르', '함량_원료성분원문': '총량 : 1캡슐(1,000 mg) 중|성분명 : 디히드록시디부틸에테르|분량 : 500|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(975 mg) 중|성분명 : 디히드록시디부틸에테르|분량 : 500|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1캡슐(1,000 mg) 중-내수용, 수출용1/1캡슐(975 mg) 중-수출용2', '수집URL': 'https://drug.hospitalk.net/item/198802326', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198802326', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202502925', 'ITEM_NAME': '가렌쿨캡슐(에르도스테인)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '에르도스테인', 'ENTP_NAME': '경남제약(주)', 'CHART': '흰색 내지 거의 흰색의 가루가 들어있는 상부 초록색, 하부 노랑색의 경질캡슐', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806476041002,8806476041019', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M086745]에르도스테인', '함량_원료성분원문': '총량 : 1캡슐427.0밀리그램|성분명 : 에르도스테인|분량 : 300.0|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1427.0', '수집URL': 'https://drug.hospitalk.net/item/202502925', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202502925', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200404344', 'ITEM_NAME': '가쁘레엑스과립(인삼패독산)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '길경;지각;독활;전호;시호;감초;강활;천궁;복령;인삼', 'ENTP_NAME': '경방신약(주)', 'CHART': '담갈색의 과립제', 'CHANGE_DATE': '2020-06-05', 'BAR_CODE': '8806613000107,8806613000114,8806613000121,8806613000138,8806613000145,8806613000152,8806613000169,8806613000176', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040048]길경|[M051351]지각|[M050227]독활|[M051318]전호|[M040336]시호|[M040006]감초|[M050022]강활|[M040550]천궁|[M040225]복령|[M051291]인삼', '함량_원료성분원문': '총량 : 1회3.0그램|성분명 : 인삼|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 복령|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 천궁|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 강활|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 감초|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 시호|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 전호|분량 : 1.25|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회3.0그램|성분명 : 독활|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 지각|분량 : 1.25|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회3.0그램|성분명 : 길경|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '13.0', '수집URL': 'https://drug.hospitalk.net/item/200404344', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200404344', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198601346', 'ITEM_NAME': '가소콜액(시메티콘)(군납용 : 시메티콘현탁액500밀리리터, SimethiconeOralSuspension500ml)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시메티콘', 'ENTP_NAME': '(주)태준제약', 'CHART': '유백색의 현탁제', 'CHANGE_DATE': '2022-03-31', 'BAR_CODE': '8806501000202,8806501000219,8806501000226,8806501000233,8806501000240,8806501000257,8806501000264', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223083]시메티콘|[M223083]시메티콘|[M223083]시메티콘', '함량_원료성분원문': '총량 : 이 약 100밀리리터 중|성분명 : 시메티콘|분량 : 2.0|단위 : 그램|규격 : USP|성분정보 : ;총량 : 이 약 100밀리리터 중|성분명 : 시메티콘|분량 : 2.0|단위 : 그램|규격 : USP|성분정보 : ;총량 : 이 약 100밀리리터 중|성분명 : 시메티콘|분량 : 2.0|단위 : 그램|규격 : USP|성분정보 :', '함량_총량기준': '이 약 100밀리리터 중-파우치(딸기향)10mL/이 약 100밀리리터 중-병(딸기향)500mL/이 약 100밀리리터 중-수출용', '수집URL': 'https://drug.hospitalk.net/item/198601346', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198601346', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201908292', 'ITEM_NAME': '가스부틴정100mg(트리메부틴말레산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '트리메부틴말레산염', 'ENTP_NAME': '주식회사케이에스제약', 'CHART': '흰색의 원형 정제', 'CHANGE_DATE': '2020-09-30', 'BAR_CODE': '8800590000105,8800590000112,8800590000129,8800590000136', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M252787]트리메부틴말레산염', '함량_원료성분원문': '총량 : 1정220밀리그램|성분명 : 트리메부틴말레산염|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1220', '수집URL': 'https://drug.hospitalk.net/item/201908292', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201908292', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202302463', 'ITEM_NAME': '가스앤드액(시메티콘)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시메티콘', 'ENTP_NAME': '유니메드제약(주)', 'CHART': '알루미늄호일 파우치에 들어있는 딸기향이 나는 유백색의 현탁제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806495084004,8806495084011,8806495084028', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223083]시메티콘', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 시메티콘|분량 : 2|단위 : 그램|규격 : USP|성분정보 :', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/202302463', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202302463', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201700141', 'ITEM_NAME': '가스엑션쓰리연질캡슐(시메티콘)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시메티콘', 'ENTP_NAME': '(주)서흥', 'CHART': '반투명한 흰색 내용물이 들어있는 보라색의 타원형 연질캡슐', 'CHANGE_DATE': '미기재', 'BAR_CODE': '미기재', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223083]시메티콘', '함량_원료성분원문': '총량 : 1캡슐(400mg)중|성분명 : 시메티콘|분량 : 250|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1캡슐(400mg)중', '수집URL': 'https://drug.hospitalk.net/item/201700141', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201700141', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201602608', 'ITEM_NAME': '가스엑션연질캡슐(시메티콘)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시메티콘', 'ENTP_NAME': '(주)서흥', 'CHART': '반투명한 흰색 내용물이 들어있는 연두색의 타원형 연질캡슐', 'CHANGE_DATE': '미기재', 'BAR_CODE': '미기재', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223083]시메티콘', '함량_원료성분원문': '총량 : 1캡슐(225mg)중|성분명 : 시메티콘|분량 : 125|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1캡슐(225mg)중', '수집URL': 'https://drug.hospitalk.net/item/201602608', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201602608', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201700142', 'ITEM_NAME': '가스엑션투연질캡슐(시메티콘)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시메티콘', 'ENTP_NAME': '(주)서흥', 'CHART': '반투명한 흰색 내용물이 들어있는 주황색의 타원형 연질캡슐', 'CHANGE_DATE': '미기재', 'BAR_CODE': '미기재', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223083]시메티콘', '함량_원료성분원문': '총량 : 1캡슐(320mg)중|성분명 : 시메티콘|분량 : 180.0|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1캡슐(320mg)중', '수집URL': 'https://drug.hospitalk.net/item/201700142', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201700142', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201801490', 'ITEM_NAME': '가스콘액(시메티콘)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시메티콘', 'ENTP_NAME': '(주)텔콘알에프제약', 'CHART': '알루미늄호일 파우치에 들어있는 딸기향이 나는 유백색의 현탁제', 'CHANGE_DATE': '2022-03-31', 'BAR_CODE': '8806255005805,8806255005812,8806255005829,8806255005836,8806255005843', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223083]시메티콘', '함량_원료성분원문': '총량 : 100mL 중|성분명 : 시메티콘|분량 : 2|단위 : 그램|규격 : USP|성분정보 :', '함량_총량기준': '100mL 중', '수집URL': 'https://drug.hospitalk.net/item/201801490', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201801490', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201501890', 'ITEM_NAME': '가스큐액(시메티콘)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시메티콘', 'ENTP_NAME': '주식회사제뉴원사이언스', 'CHART': '유백색의 현탁액', 'CHANGE_DATE': '2022-03-31', 'BAR_CODE': '8806717046308,8806717046315,8806717046322,8806717046339,8806717046346,8806717046353,8806717046360', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223083]시메티콘|[M223083]시메티콘', '함량_원료성분원문': '총량 : 이 약 100mL 중|성분명 : 시메티콘|분량 : 2|단위 : 그램|규격 : USP|성분정보 : ;총량 : 이 약 100mL 중|성분명 : 시메티콘|분량 : 2|단위 : 그램|규격 : USP|성분정보 :', '함량_총량기준': '이 약 100mL 중-병포장/이 약 100mL 중-파우치포장(1회용)', '수집URL': 'https://drug.hospitalk.net/item/201501890', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201501890', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200300066', 'ITEM_NAME': '가스키환(연라환)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '향부자;도인;천궁;아출;삼릉;치자;내복자;개자;황련;산사;신곡;청피;오수유;익지', 'ENTP_NAME': '(주)한풍제약', 'CHART': '갈색의 환제', 'CHANGE_DATE': '2025-06-19', 'BAR_CODE': '8806581000406,8806581000413,8806581000420,8806581000437,8806581049108,8806581049115,8806581049122', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040228]향부자|[M040086]도인|[M040550]천궁|[M088722]아출|[M050747]삼릉|[M040564]치자|[M210181]내복자|[M040012]개자|[M040792]황련|[M050729]산사|[M050891]신곡|[M051394]청피|[M040447]오수유|[M040507]익지', '함량_원료성분원문': '총량 : 1회3.9그램|성분명 : 황련|분량 : 432|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.9그램|성분명 : 산사|분량 : 288|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.9그램|성분명 : 신곡|분량 : 288|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1회3.9그램|성분명 : 청피|분량 : 144|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.9그램|성분명 : 오수유|분량 : 144|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.9그램|성분명 : 익지|분량 : 144|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.9그램|성분명 : 개자|분량 : 432|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1회3.9그램|성분명 : 내복자|분량 : 432|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.9그램|성분명 : 치자|분량 : 288|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.9그램|성분명 : 삼릉|분량 : 288|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.9그램|성분명 : 아출|분량 : 288|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.9그램|성분명 : 천궁|분량 : 288|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.9그램|성분명 : 도인|분량 : 288|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.9그램|성분명 : 향부자|분량 : 288|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '13.9', '수집URL': 'https://drug.hospitalk.net/item/200300066', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200300066', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201400237', 'ITEM_NAME': '가스트로겔현탁액(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '수산화마그네슘;건조수산화알루미늄 겔;옥세타자인;건조수산화알루미늄겔', 'ENTP_NAME': '(주)테라젠이텍스', 'CHART': '[수출용1]향기가 있는 흰색의 현탁액 [수출용2]알루미늄 포에 든 흰색의 현탁제', 'CHANGE_DATE': '2024-09-24', 'BAR_CODE': '8806985026309,8806985026316', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040306]수산화마그네슘|[M229291]건조수산화알루미늄 겔|[M201415]옥세타자인|[M201415]옥세타자인|[M040306]수산화마그네슘|[M040308]건조수산화알루미늄겔', '함량_원료성분원문': '총량 : [수출용1] 이 약 100mL 중|성분명 : 건조수산화알루미늄겔|분량 : 5.82|단위 : 그램|규격 : KP|성분정보 : 산화알루미늄(Al2O3)으로서 2.91g;총량 : [수출용1] 이 약 100mL 중|성분명 : 수산화마그네슘|분량 : 1.96|단위 : 그램|규격 : USP|성분정보 : ;총량 : [수출용1] 이 약 100mL 중|성분명 : 옥세타자인|분량 : 0.2|단위 : 그램|규격 : KP|성분정보 : ;총량 : 10밀리리터1포|성분명 : 옥세타자인|분량 : 20|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 10밀리리터1포|성분명 : 건조수산화알루미늄 겔|분량 : 582|단위 : 밀리그램|규격 : KP|성분정보 : 산화알루미늄으로서 291밀리그램;총량 : 10밀리리터1포|성분명 : 수산화마그네슘|분량 : 196|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '[수출용1] 이 약 100mL 중-[수출용1]/101-[수출용2]', '수집URL': 'https://drug.hospitalk.net/item/201400237', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201400237', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202601758', 'ITEM_NAME': '가스트릴정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '옥세타자인;탄산마그네슘;건조수산화알루미늄 겔', 'ENTP_NAME': '메딕스제약(주)', 'CHART': '흰색의 원형 정제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806258020102,8806258020119', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M201415]옥세타자인|[M040629]탄산마그네슘|[M229291]건조수산화알루미늄 겔', '함량_원료성분원문': '총량 : 1정360밀리그램|성분명 : 건조수산화알루미늄 겔|분량 : 124.9|단위 : 밀리그램|규격 : KP|성분정보 : 산화알루미늄(으)로서 62.45 밀리그램;총량 : 1정360밀리그램|성분명 : 탄산마그네슘|분량 : 83.8|단위 : 밀리그램|규격 : KP|성분정보 : 산화마그네슘(으)로서 35.2 밀리그램;총량 : 1정360밀리그램|성분명 : 옥세타자인|분량 : 5|단위 : 밀리그램|규격 : JP|성분정보 :', '함량_총량기준': '1360', '수집URL': 'https://drug.hospitalk.net/item/202601758', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202601758', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202102261', 'ITEM_NAME': '가스트큐정(반하사심탕)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '황련;대추;감초;인삼;건강;황금;반하', 'ENTP_NAME': '(주)알피바이오', 'CHART': '갈색의 장방형 코팅정제', 'CHANGE_DATE': '2022-11-22', 'BAR_CODE': '8806616055005,8806616055012', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040792]황련|[M040071]대추|[M040006]감초|[M051291]인삼|[M040007]건강|[M040789]황금|[M040202]반하', '함량_원료성분원문': '총량 : 1정650밀리그램|성분명 : 반하|분량 : 835.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정650밀리그램|성분명 : 황금|분량 : 500.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정650밀리그램|성분명 : 건강|분량 : 415.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정650밀리그램|성분명 : 인삼|분량 : 500.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정650밀리그램|성분명 : 감초|분량 : 500.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정650밀리그램|성분명 : 대추|분량 : 500.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정650밀리그램|성분명 : 황련|분량 : 165.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1650', '수집URL': 'https://drug.hospitalk.net/item/202102261', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202102261', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200904519', 'ITEM_NAME': '간모아액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '베타인;베타인염산염;시트르산수화물;L-아르기닌', 'ENTP_NAME': '경진제약(주)', 'CHART': '알루미늄포 또는 유리병에 든 연한 담갈색의 경구용 액제', 'CHANGE_DATE': '2026-05-28', 'BAR_CODE': '8806226001201,8806226001218,8806226001225,8806604029100,8806604029117,8806604029124,8806604029131,8806633005106,8806717031205,8806717031212,8806717031229', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050571]베타인|[M241790]베타인염산염|[M223090]시트르산수화물|[M103077]L-아르기닌', '함량_원료성분원문': '총량 : 100mL 중|성분명 : L-아르기닌|분량 : 7.31|단위 : 그램|규격 : USP|성분정보 : ;총량 : 100mL 중|성분명 : 시트르산수화물|분량 : 2.94|단위 : 그램|규격 : KP|성분정보 : ;총량 : 100mL 중|성분명 : 베타인염산염|분량 : 5|단위 : 그램|규격 : USP|성분정보 : 베타인으로서 3.8135g;총량 : 100mL 중|성분명 : 베타인|분량 : 5|단위 : 그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '100mL 중', '수집URL': 'https://drug.hospitalk.net/item/200904519', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200904519', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201800788', 'ITEM_NAME': '간프로액(L-아스파르트산-L-오르니틴)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': 'L-아스파르트산-L-오르니틴', 'ENTP_NAME': '(주)유유제약', 'CHART': '알루미늄 호일 파우치에 들어있는 엷은 갈색의 액체', 'CHANGE_DATE': '2021-06-07', 'BAR_CODE': '8806445025408,8806445025415,8806445025422,8806445025439', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M254056]L-아스파르트산-L-오르니틴', '함량_원료성분원문': '총량 : 이 약 1포(15g) 중|성분명 : L-아스파르트산-L-오르니틴|분량 : 3.0|단위 : 그램|규격 : DAB|성분정보 :', '함량_총량기준': '이 약 1포(15g) 중', '수집URL': 'https://drug.hospitalk.net/item/201800788', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201800788', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200904336', 'ITEM_NAME': '갈마겔현탁액(알마게이트)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '알마게이트', 'ENTP_NAME': '주식회사제뉴원사이언스', 'CHART': '흰색의 현탁제', 'CHANGE_DATE': '2017-09-11', 'BAR_CODE': '8806717027505,8806717027512,8806717027529', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081294]알마게이트|[M081294]알마게이트', '함량_원료성분원문': '총량 : 이 약 1포(15밀리리터) 중|성분명 : 알마게이트|분량 : 1.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 이 약 1포(15밀리리터) 중|성분명 : 알마게이트|분량 : 1.5|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 1포(15밀리리터) 중-1.내수용/이 약 1포(15밀리리터) 중-2.수출용1', '수집URL': 'https://drug.hospitalk.net/item/200904336', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200904336', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '197600614', 'ITEM_NAME': '갈타제산(베타-갈락토시다제(아스퍼길루스))', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '베타-갈락토시다제(아스퍼길루스)', 'ENTP_NAME': '현대약품(주)', 'CHART': '백색-담황색의 가루로 특이한 냄새가 있으며 약간 단맛이 있다.', 'CHANGE_DATE': '2015-10-20', 'BAR_CODE': '8806420000109,8806420000116,8806420000123,8806420000130,8806420000147,8806420000154', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M262955]베타-갈락토시다제(아스퍼길루스)', '함량_원료성분원문': '총량 : 1그램 중|성분명 : 베타-갈락토시다제(아스퍼길루스)|분량 : 5,000|단위 : |규격 : JP|성분정보 :', '함량_총량기준': '1그램 중', '수집URL': 'https://drug.hospitalk.net/item/197600614', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=197600614', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202401444', 'ITEM_NAME': '갈해담액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '구아이페네신;길경;원지;인삼;마황', 'ENTP_NAME': '제일헬스사이언스(주)', 'CHART': '이 약은 갈색의 액제이다.', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8800543013404,8800543013411,8800543013428', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050058]구아이페네신|[M040048]길경|[M040482]원지|[M051291]인삼|[M040135]마황', '함량_원료성분원문': '총량 : 1포15밀리리터|성분명 : 마황|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포15밀리리터|성분명 : 인삼|분량 : 0.2|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포15밀리리터|성분명 : 원지|분량 : 0.17|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포15밀리리터|성분명 : 길경|분량 : 0.3|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포15밀리리터|성분명 : 구아이페네신|분량 : 70|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '115', '수집URL': 'https://drug.hospitalk.net/item/202401444', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202401444', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201500053', 'ITEM_NAME': '감마마그빅연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': 'γ-오리자놀;피리독신염산염;티아민질산염;산화마그네슘;토코페롤아세테이트', 'ENTP_NAME': '알파제약(주)', 'CHART': '회백색의 유상물질이 들어있는 적갈색의 장방형 연질캡슐제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806542021808,8806542021815', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M208932]γ-오리자놀|[M204304]피리독신염산염|[M223262]티아민질산염|[M040262]산화마그네슘|[M223240]토코페롤아세테이트', '함량_원료성분원문': '총량 : 1캡슐(1,712.4 밀리그램) 중|성분명 : γ-오리자놀|분량 : 5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,712.4 밀리그램) 중|성분명 : 피리독신염산염|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,712.4 밀리그램) 중|성분명 : 티아민질산염|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,712.4 밀리그램) 중|성분명 : 산화마그네슘|분량 : 250.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,712.4 밀리그램) 중|성분명 : 토코페롤아세테이트|분량 : 500.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1캡슐(1,712.4 밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201500053', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201500053', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199000210', 'ITEM_NAME': '감막트연질캡슐(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아스코르브산;레티놀팔미테이트;토코페롤아세테이트;셀레늄함유건조효모', 'ENTP_NAME': '(주)유유제약', 'CHART': '미황색 유상 내용물이 들어 있는 좌-초록색과 우- 초코렛색의 타원형 연질캅셀', 'CHANGE_DATE': '2014-10-07', 'BAR_CODE': '8806445000207', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M258994]아스코르브산|[M222991]레티놀팔미테이트|[M223240]토코페롤아세테이트|[M089702]셀레늄함유건조효모', '함량_원료성분원문': '총량 : 1캅셀(내용량 1190 밀리그램) 중|성분명 : 셀레늄함유건조효모|분량 : 92.6|단위 : 밀리그램|규격 : KP|성분정보 : 셀레늄으로서 50ug;총량 : 1캅셀(내용량 1190 밀리그램) 중|성분명 : 토코페롤아세테이트|분량 : 400|단위 : 아이.유|규격 : KP|성분정보 : ;총량 : 1캅셀(내용량 1190 밀리그램) 중|성분명 : 레티놀팔미테이트|분량 : 5000|단위 : 아이.유|규격 : KP|성분정보 : ;총량 : 1캅셀(내용량 1190 밀리그램) 중|성분명 : 아스코르브산|분량 : 500|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1캅셀(내용량 1190 밀리그램) 중/1캅셀(내용량 1190 밀리그램) 중-연질캅셀성분', '수집URL': 'https://drug.hospitalk.net/item/199000210', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199000210', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200004479', 'ITEM_NAME': '감바로과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '에텐자미드;건강;감초;작약;육계;대추;마황;카페인무수물;노스카핀;클로르페니라민말레산염;갈근', 'ENTP_NAME': '한솔신약(주)', 'CHART': '갈색의 과립제', 'CHANGE_DATE': '2023-08-22', 'BAR_CODE': '8806458000102,8806458000119,8806458000126,8806458000140', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040417]에텐자미드|[M040007]건강|[M040006]감초|[M040523]작약|[M050036]육계|[M040071]대추|[M040135]마황|[M223183]카페인무수물|[M040059]노스카핀|[M223211]클로르페니라민말레산염|[M040004]갈근', '함량_원료성분원문': '총량 : 1포(3.0그램) 중|성분명 : 갈근|분량 : 746.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그램) 중|성분명 : 클로르페니라민말레산염|분량 : 2.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그램) 중|성분명 : 노스카핀|분량 : 16|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그램) 중|성분명 : 카페인무수물|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그램) 중|성분명 : 마황|분량 : 373.3|단위 : 밀리그램|규격 : KP|성분정보 : 총알칼로이드(에페드린 및 슈도에페드린)으로서 2.61mg;총량 : 1포(3.0그램) 중|성분명 : 대추|분량 : 373.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그램) 중|성분명 : 육계|분량 : 280|단위 : 밀리그램|규격 : KP|성분정보 : 신남산으로서 0.084mg;총량 : 1포(3.0그램) 중|성분명 : 작약|분량 : 280|단위 : 밀리그램|규격 : KP|성분정보 : 패오니플로린으로서 5.6mg;총량 : 1포(3.0그램) 중|성분명 : 감초|분량 : 186.7|단위 : 밀리그램|규격 : KP|성분정보 : 글리시리진산으로서 4.67mg;총량 : 1포(3.0그램) 중|성분명 : 건강|분량 : 93.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그램) 중|성분명 : 에텐자미드|분량 : 360|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1포(3.0그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200004479', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200004479', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202601926', 'ITEM_NAME': '감비산', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건강;감초;목단피;반하;대황;승마;작약;택사;저령;육계;시호', 'ENTP_NAME': '(주)티디에스팜', 'CHART': '담갈색의 산제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806798023304,8806798023311,8806798023328', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040007]건강|[M040006]감초|[M040185]목단피|[M040202]반하|[M040073]대황|[M040329]승마|[M040523]작약|[M040638]택사|[M051313]저령|[M050036]육계|[M040336]시호', '함량_원료성분원문': '총량 : 1포2.3그램|성분명 : 시호|분량 : 286|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 육계|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 저령|분량 : 286|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 택사|분량 : 286|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 작약|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 승마|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 대황|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 반하|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 목단피|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 감초|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 건강|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '12.3', '수집URL': 'https://drug.hospitalk.net/item/202601926', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202601926', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200809221', 'ITEM_NAME': '감치원-골드액(십신탕액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '갈근;진피;마황;승마;자소엽;향부자;감초;천궁;생강;백지;작약', 'ENTP_NAME': '(주)한국신약', 'CHART': '생약의 독특한 맛과 향취가 있는 적갈색의 액제', 'CHANGE_DATE': '2010-03-09', 'BAR_CODE': '8806550058308,8806550058315,8806550058322', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040004]갈근|[M040538]진피|[M040135]마황|[M040329]승마|[M051301]자소엽|[M040228]향부자|[M040006]감초|[M040550]천궁|[M050752]생강|[M040216]백지|[M040523]작약', '함량_원료성분원문': '총량 : 1포 (75밀리리터) 중|성분명 : 작약|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 (75밀리리터) 중|성분명 : 백지|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 (75밀리리터) 중|성분명 : 생강|분량 : 0.5|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포 (75밀리리터) 중|성분명 : 천궁|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 (75밀리리터) 중|성분명 : 감초|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 (75밀리리터) 중|성분명 : 향부자|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 (75밀리리터) 중|성분명 : 자소엽|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 (75밀리리터) 중|성분명 : 승마|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 (75밀리리터) 중|성분명 : 마황|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 (75밀리리터) 중|성분명 : 진피|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 (75밀리리터) 중|성분명 : 갈근|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1포 (75밀리리터) 중', '수집URL': 'https://drug.hospitalk.net/item/200809221', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200809221', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200902216', 'ITEM_NAME': '감코날액(소청룡탕액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '오미자;세신;계지;감초;건강;마황;작약;반하', 'ENTP_NAME': '(주)한국신약', 'CHART': '파우치에 포장된 생약의 특이한 맛과 향취가 있는 갈색의 액제', 'CHANGE_DATE': '2009-04-27', 'BAR_CODE': '8806550059305,8806550059312,8806550059329,8806550059336', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040445]오미자|[M040293]세신|[M050037]계지|[M040006]감초|[M040007]건강|[M040135]마황|[M040523]작약|[M040202]반하', '함량_원료성분원문': '총량 : 1팩 (100밀리리터) 중|성분명 : 반하|분량 : 2|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1팩 (100밀리리터) 중|성분명 : 작약|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1팩 (100밀리리터) 중|성분명 : 마황|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1팩 (100밀리리터) 중|성분명 : 건강|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1팩 (100밀리리터) 중|성분명 : 감초|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1팩 (100밀리리터) 중|성분명 : 계지|분량 : 1|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1팩 (100밀리리터) 중|성분명 : 세신|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1팩 (100밀리리터) 중|성분명 : 오미자|분량 : 1|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1팩 (100밀리리터) 중', '수집URL': 'https://drug.hospitalk.net/item/200902216', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200902216', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200810939', 'ITEM_NAME': '감콜데이나이트정(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르페니라민말레산염;페닐레프린염산염;아세트아미노펜;슈도에페드린염산염', 'ENTP_NAME': '(주)마더스제약', 'CHART': '주간용 : 흰색의 장방형 필름코팅정제 야간용 : 황색의 장방형 필름코팅정제', 'CHANGE_DATE': '2019-11-04', 'BAR_CODE': '8806228000202,8806228000219,8806552015903,8806552015910', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223211]클로르페니라민말레산염|[M222724]페닐레프린염산염|[M040353]아세트아미노펜|[M223211]클로르페니라민말레산염|[M203364]슈도에페드린염산염|[M040353]아세트아미노펜', '함량_원료성분원문': '총량 : 1정 (655mg) 중|성분명 : 아세트아미노펜|분량 : 500|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 (655mg) 중|성분명 : 슈도에페드린염산염|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 (655mg) 중|성분명 : 클로르페니라민말레산염|분량 : 2|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 (655mg) 중|성분명 : 아세트아미노펜|분량 : 500|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 (655mg) 중|성분명 : 페닐레프린염산염|분량 : 5|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1정 (655mg) 중|성분명 : 클로르페니라민말레산염|분량 : 2|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정 (655mg) 중-주간용/1정 (655mg) 중-야간용', '수집URL': 'https://drug.hospitalk.net/item/200810939', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200810939', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200604208', 'ITEM_NAME': '감콜캡슐(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초엑스산(5→1);길경엑스산(10→1);덱스트로메토르판브롬화수소산염수화물;dl-메틸에페드린염산염;아세트아미노펜;클로르페니라민말레산염;메타규산알루민산마그네슘;티아민질산염;카페인무수물', 'ENTP_NAME': '(주)마더스제약', 'CHART': '갈색의 가루가 든 상하 백색의 경질캡슐제', 'CHANGE_DATE': '2018-07-05', 'BAR_CODE': '8806228001506,8806228001513,8806228001520,8806552000107,8806552000114,8806552000121', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M230816]감초엑스산(5→1)|[M101406]길경엑스산(10→1)|[M222957]덱스트로메토르판브롬화수소산염수화물|[M204422]dl-메틸에페드린염산염|[M040353]아세트아미노펜|[M223211]클로르페니라민말레산염|[M050448]메타규산알루민산마그네슘|[M223262]티아민질산염|[M223183]카페인무수물', '함량_원료성분원문': '총량 : 1캡슐 (약 400밀리그람) 중|성분명 : 카페인무수물|분량 : 20.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐 (약 400밀리그람) 중|성분명 : 티아민질산염|분량 : 4.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐 (약 400밀리그람) 중|성분명 : 메타규산알루민산마그네슘|분량 : 80.0|단위 : 밀리그램|규격 : KPC|성분정보 : 건조물로 70.4mg;총량 : 1캡슐 (약 400밀리그람) 중|성분명 : 클로르페니라민말레산염|분량 : 1.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐 (약 400밀리그람) 중|성분명 : 아세트아미노펜|분량 : 150.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐 (약 400밀리그람) 중|성분명 : dl-메틸에페드린염산염|분량 : 6.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐 (약 400밀리그람) 중|성분명 : 덱스트로메토르판브롬화수소산염수화물|분량 : 7.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐 (약 400밀리그람) 중|성분명 : 길경엑스산(10→1)|분량 : 9.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1캡슐 (약 400밀리그람) 중|성분명 : 감초엑스산(5→1)|분량 : 21.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1캡슐 (약 400밀리그람) 중', '수집URL': 'https://drug.hospitalk.net/item/200604208', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200604208', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200908839', 'ITEM_NAME': '감패탕에프액(갈근탕연조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '갈근탕연조엑스', 'ENTP_NAME': '조아제약(주)', 'CHART': '생약 특유의 맛과 향이 있는 갈색의 액체가 든 파우치 또는 유리병', 'CHANGE_DATE': '2011-05-23', 'BAR_CODE': '8806446023403,8806446023410', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M086018]갈근탕연조엑스', '함량_원료성분원문': '총량 : 이 약 75mL 중|성분명 : 갈근탕연조엑스|분량 : 2.77|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '이 약 75mL 중', '수집URL': 'https://drug.hospitalk.net/item/200908839', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200908839', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200801645', 'ITEM_NAME': '개비스콘더블액션현탁액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '탄산수소나트륨;탄산칼슘;알긴산나트륨', 'ENTP_NAME': '(유)옥시레킷벤키저', 'CHART': '페퍼민트향이 나는 미황색～크림색의 현탁액', 'CHANGE_DATE': '2021-06-01', 'BAR_CODE': '8806406000802,8806406000819,8806406000826,8806406000833,8806406000840,8806406000857', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040631]탄산수소나트륨|[M051564]탄산칼슘|[M040385]알긴산나트륨', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 알긴산나트륨|분량 : 5.00|단위 : 그램|규격 : EP|성분정보 : 건조물(으)로서 4.375 그램;총량 : 100밀리리터|성분명 : 탄산칼슘|분량 : 3.25|단위 : 그램|규격 : EP|성분정보 : ;총량 : 100밀리리터|성분명 : 탄산수소나트륨|분량 : 2.13|단위 : 그램|규격 : EP|성분정보 :', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/200801645', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200801645', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200606295', 'ITEM_NAME': '개비스콘페퍼민트현탁액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '알긴산나트륨;탄산수소나트륨;탄산칼슘', 'ENTP_NAME': '(유)옥시레킷벤키저', 'CHART': '페퍼민트향이 나는 미황색~크림색의 점조성 현탁액', 'CHANGE_DATE': '2020-03-31', 'BAR_CODE': '8806406000208,8806406000215,8806406000222,8806406000239,8806406000246', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040385]알긴산나트륨|[M040631]탄산수소나트륨|[M051564]탄산칼슘', '함량_원료성분원문': '총량 : 전과 동일-이 약 100밀리리터 중|성분명 : 알긴산나트륨|분량 : 5.000|단위 : 그램|규격 : EP|성분정보 : ;총량 : 전과 동일-이 약 100밀리리터 중|성분명 : 탄산수소나트륨|분량 : 2.670|단위 : 그램|규격 : EP|성분정보 : ;총량 : 전과 동일-이 약 100밀리리터 중|성분명 : 탄산칼슘|분량 : 1.600|단위 : 그램|규격 : EP|성분정보 :', '함량_총량기준': '전과 동일-이 약 100밀리리터 중-포', '수집URL': 'https://drug.hospitalk.net/item/200606295', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200606295', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200200228', 'ITEM_NAME': '개비콘큐츄어블정(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '스코폴리아엑스;규산마그네슘;건조수산화알루미늄겔', 'ENTP_NAME': '(주)유유제약', 'CHART': '버터스카치향을 지닌 백색의 원형 정제', 'CHANGE_DATE': '2014-10-21', 'BAR_CODE': '8806445000504', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M080221]스코폴리아엑스|[M040038]규산마그네슘|[M040308]건조수산화알루미늄겔', '함량_원료성분원문': '총량 : 1 정(1,600 mg) 중|성분명 : 건조수산화알루미늄겔|분량 : 80.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1 정(1,600 mg) 중|성분명 : 규산마그네슘|분량 : 20.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1 정(1,600 mg) 중|성분명 : 스코폴리아엑스|분량 : 5.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1 정(1,600 mg) 중', '수집URL': 'https://drug.hospitalk.net/item/200200228', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200200228', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200000366', 'ITEM_NAME': '개스판연질캡슐(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '캐레웨이유;페파민트유', 'ENTP_NAME': '(주)유유제약', 'CHART': '무색의 유상내용물이 들어있는 담록색의 타원형 연질캅셀', 'CHANGE_DATE': '2014-10-13', 'BAR_CODE': '8806445000603', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M071401]캐레웨이유|[M089664]페파민트유', '함량_원료성분원문': '총량 : 이 약 1캡슐 (322mg) 중|성분명 : 캐레웨이유|분량 : 50.0|단위 : 밀리그램|규격 : DAB|성분정보 : ;총량 : 이 약 1캡슐 (322mg) 중|성분명 : 페파민트유|분량 : 90.0|단위 : 밀리그램|규격 : EP|성분정보 :', '함량_총량기준': '이 약 1캡슐 (322mg) 중', '수집URL': 'https://drug.hospitalk.net/item/200000366', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200000366', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '197400369', 'ITEM_NAME': '개풍경옥고(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '꿀;침향가루;구기자가루;복령가루;인삼가루;생지황의 착즙', 'ENTP_NAME': '광동제약(주)', 'CHART': '이 약은 흑갈색의 유동성 연조엑스상의 물질로서 특이한 냄새가 있고 맛은 달고 조금 쓰다. 이 약은 물에 조금 혼탁시켜 녹이면 유갈색의 액이 된다.', 'CHANGE_DATE': '1988-02-22', 'BAR_CODE': '8806418000500,8806418000517,8806418000524,8806418000531', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M200168]꿀|[M084957]침향가루|[M091785]구기자가루|[M082760]복령가루|[M082761]인삼가루|[M248799]생지황의 착즙', '함량_원료성분원문': '총량 : 100 그램 중|성분명 : 생지황의 착즙|분량 : 32.0|단위 : 그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 100 그램 중|성분명 : 인삼가루|분량 : 2.8|단위 : 그램|규격 : JP|성분정보 : ;총량 : 100 그램 중|성분명 : 복령가루|분량 : 8.0|단위 : 그램|규격 : JP|성분정보 : ;총량 : 100 그램 중|성분명 : 구기자가루|분량 : 0.9|단위 : 그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 100 그램 중|성분명 : 침향가루|분량 : 0.1|단위 : 그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 100 그램 중|성분명 : 꿀|분량 : 38.5|단위 : 그램|규격 : JP|성분정보 :', '함량_총량기준': '100 그램 중', '수집URL': 'https://drug.hospitalk.net/item/197400369', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=197400369', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201700245', 'ITEM_NAME': '건아이점안액(폴리소르베이트80)(1회용)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '폴리소르베이트 80', 'ENTP_NAME': '유니메드제약(주)', 'CHART': '무색투명 플라스틱 용기에 무색투명한 액이 든 점안제', 'CHANGE_DATE': '2026-09-28', 'BAR_CODE': '8806495073404,8806495073411,8806495073428', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M214655]폴리소르베이트 80', '함량_원료성분원문': '총량 : 이 약 1밀리리터 중|성분명 : 폴리소르베이트 80|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 1밀리리터 중', '수집URL': 'https://drug.hospitalk.net/item/201700245', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201700245', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005882', 'ITEM_NAME': '건양탕(반하후박탕엑스과립)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '생강;자소엽;복령;후박;반하', 'ENTP_NAME': '경방신약(주)', 'CHART': '담갈색의 과립제', 'CHANGE_DATE': '2019-10-28', 'BAR_CODE': '8806613000602,8806613000619,8806613000626,8806613000633,8806613000640,8806613000657,8806613000664,8806613000671', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050752]생강|[M051301]자소엽|[M040225]복령|[M040813]후박|[M040202]반하', '함량_원료성분원문': '총량 : 1회2.0그램|성분명 : 반하|분량 : 2.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회2.0그램|성분명 : 후박|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회2.0그램|성분명 : 복령|분량 : 1.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회2.0그램|성분명 : 자소엽|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회2.0그램|성분명 : 생강|분량 : 1.33|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '12.0', '수집URL': 'https://drug.hospitalk.net/item/200005882', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005882', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202302051', 'ITEM_NAME': '건일이부프로펜연질캡슐400밀리그램', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '이부프로펜', 'ENTP_NAME': '건일제약(주)', 'CHART': '무색 내지 엷은 청색의 액상 내용물이 든 청색의 투명한 타원형 연질캡슐', 'CHANGE_DATE': '2025-10-10', 'BAR_CODE': '8806468032209,8806468032216', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051259]이부프로펜', '함량_원료성분원문': '총량 : 1캡슐1,110밀리그램|성분명 : 이부프로펜|분량 : 400|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '11,110', '수집URL': 'https://drug.hospitalk.net/item/202302051', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202302051', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200100065', 'ITEM_NAME': '건치환', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '박하;형개;목단피;치자;황련;생지황;작약;천궁;감초;방풍;당귀', 'ENTP_NAME': '(주)한풍제약', 'CHART': '흑갈색의 환제이다.', 'CHANGE_DATE': '2023-11-27', 'BAR_CODE': '8806581000802,8806581000819,8806581000826,8806581000833,8806581049009,8806581049016,8806581049023,8806581049030,8806581049047', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040198]박하|[M051936]형개|[M040185]목단피|[M040564]치자|[M040792]황련|[M051363]생지황|[M040523]작약|[M040550]천궁|[M040006]감초|[M040205]방풍|[M040070]당귀', '함량_원료성분원문': '총량 : 1환(130mg) 중|성분명 : 당귀|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(130mg) 중|성분명 : 방풍|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(130mg) 중|성분명 : 감초|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : 글리시리진산으로서 1.56mg;총량 : 1환(130mg) 중|성분명 : 천궁|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(130mg) 중|성분명 : 작약|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : 패오니플로린으로서 1.25mg;총량 : 1환(130mg) 중|성분명 : 생지황|분량 : 62.5|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(130mg) 중|성분명 : 황련|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : 베르베린(염화베르베린)으로서 2.63mg;총량 : 1환(130mg) 중|성분명 : 치자|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : 게니포시드로서 1.88mg;총량 : 1환(130mg) 중|성분명 : 목단피|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : 패오니플로린으로서 0.31mg;총량 : 1환(130mg) 중|성분명 : 형개|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(130mg) 중|성분명 : 박하|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1환(130mg) 중', '수집URL': 'https://drug.hospitalk.net/item/200100065', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200100065', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199501099', 'ITEM_NAME': '게루삼엠정(건조수산화알루미늄겔)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건조수산화알루미늄 겔', 'ENTP_NAME': '삼남제약(주)', 'CHART': '백색의 원형 정제', 'CHANGE_DATE': '2009-10-01', 'BAR_CODE': '8806537003802,8806537003819,8806537003826,8806537003833,8806537003840,8806537003857,8806537003864', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M229291]건조수산화알루미늄 겔', '함량_원료성분원문': '총량 : 1정(450mg) 중|성분명 : 건조수산화알루미늄 겔|분량 : 392.0|단위 : 밀리그램|규격 : KP|성분정보 : 수산화알루미늄으로서 300밀리그램', '함량_총량기준': '1정(450mg) 중', '수집URL': 'https://drug.hospitalk.net/item/199501099', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199501099', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '196400046', 'ITEM_NAME': '게루삼정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '탄산수소나트륨;탄산마그네슘;침강탄산칼슘;건조수산화알루미늄 겔', 'ENTP_NAME': '삼남제약(주)', 'CHART': '흰색의 원형정제', 'CHANGE_DATE': '2019-12-20', 'BAR_CODE': '8806537000603,8806537000610,8806537000627', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M207094]탄산수소나트륨|[M040629]탄산마그네슘|[M040634]침강탄산칼슘|[M229291]건조수산화알루미늄 겔', '함량_원료성분원문': '총량 : 1정(430mg) 중|성분명 : 건조수산화알루미늄 겔|분량 : 200.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(430mg) 중|성분명 : 침강탄산칼슘|분량 : 100.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(430mg) 중|성분명 : 탄산마그네슘|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(430mg) 중|성분명 : 탄산수소나트륨|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정(430mg) 중', '수집URL': 'https://drug.hospitalk.net/item/196400046', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=196400046', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200100078', 'ITEM_NAME': '게리단환(계지복령환)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '계지;작약;복령;목단피;도인', 'ENTP_NAME': '(주)한풍제약', 'CHART': '갈색의 소형환제', 'CHANGE_DATE': '2024-02-20', 'BAR_CODE': '8806581000901,8806581000918,8806581000925,8806581000932,8806581000949', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050037]계지|[M040523]작약|[M040225]복령|[M040185]목단피|[M040086]도인', '함량_원료성분원문': '총량 : 1회2.4그램|성분명 : 도인|분량 : 400.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회2.4그램|성분명 : 목단피|분량 : 400.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회2.4그램|성분명 : 복령|분량 : 400.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회2.4그램|성분명 : 작약|분량 : 400.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회2.4그램|성분명 : 계지|분량 : 400.0|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '12.4', '수집URL': 'https://drug.hospitalk.net/item/200100078', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200100078', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199806929', 'ITEM_NAME': '게리동정(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아세트아미노펜;에텐자미드;카페인무수물;클로르페니라민말레산염', 'ENTP_NAME': '(주)넥스팜코리아', 'CHART': '분홍색 삼각형 정제', 'CHANGE_DATE': '2015-01-31', 'BAR_CODE': '8806625000300,8806625000317,8806625000324,8806625000331', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040353]아세트아미노펜|[M040417]에텐자미드|[M223183]카페인무수물|[M223211]클로르페니라민말레산염', '함량_원료성분원문': '총량 : 1정 (550mg)중|성분명 : 아세트아미노펜|분량 : 200|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 (550mg)중|성분명 : 에텐자미드|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 (550mg)중|성분명 : 카페인무수물|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 (550mg)중|성분명 : 클로르페니라민말레산염|분량 : 2|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정 (550mg)중', '수집URL': 'https://drug.hospitalk.net/item/199806929', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199806929', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200401853', 'ITEM_NAME': '게리브론300장용성연질캡슐(미르톨)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '미르톨', 'ENTP_NAME': '(주)셀릭스', 'CHART': '미황색 액이 충진된 녹색의 타원형 연질캡슐', 'CHANGE_DATE': '2011-03-18', 'BAR_CODE': '8806462000204,8806462000211,8806462000228,8806462000235', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M096297]미르톨', '함량_원료성분원문': '총량 : 1캡슐(527mg) 중|성분명 : 미르톨|분량 : 300|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1캡슐(527mg) 중', '수집URL': 'https://drug.hospitalk.net/item/200401853', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200401853', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199701758', 'ITEM_NAME': '게리브론연질캡슐(미르톨)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '미르톨', 'ENTP_NAME': '(주)셀릭스', 'CHART': '미황색의 액이 충진된 녹색의 타원형 연질캡슐제', 'CHANGE_DATE': '2007-04-20', 'BAR_CODE': '8806462000303,8806462000310,8806462000327,8806462000334,8806462000341', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M096297]미르톨', '함량_원료성분원문': '총량 : 1캡슐(351mg) 중|성분명 : 미르톨|분량 : 120|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1캡슐(351mg) 중', '수집URL': 'https://drug.hospitalk.net/item/199701758', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199701758', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202007294', 'ITEM_NAME': '게보린릴랙스연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '이부프로펜;산화마그네슘', 'ENTP_NAME': '삼진제약(주)', 'CHART': '일부분 회백색의 유상내용물, 일부분 무색의 투명한 액을 함유한 주황색의 장방형 연질캡슐', 'CHANGE_DATE': '2025-10-10', 'BAR_CODE': '8806478050705,8806478050712', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051259]이부프로펜|[M040262]산화마그네슘', '함량_원료성분원문': '총량 : 1캡슐1,545밀리그램|성분명 : 이부프로펜|분량 : 400.00|단위 : 밀리그램|규격 : BP|성분정보 : ;총량 : 1캡슐1,545밀리그램|성분명 : 산화마그네슘|분량 : 80.00|단위 : 밀리그램|규격 : KP|성분정보 : 마그네슘으로서 48.25mg', '함량_총량기준': '11,545', '수집URL': 'https://drug.hospitalk.net/item/202007294', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202007294', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202107495', 'ITEM_NAME': '게보린브이정(아세트아미노펜)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아세트아미노펜', 'ENTP_NAME': '삼진제약(주)', 'CHART': '흰색의 삼각형 필름코팅정제', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806478053300,8806478053317', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040353]아세트아미노펜', '함량_원료성분원문': '총량 : 1정640.0밀리그램|성분명 : 아세트아미노펜|분량 : 500.0|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1640.0', '수집URL': 'https://drug.hospitalk.net/item/202107495', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202107495', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201908295', 'ITEM_NAME': '게보린소프트연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '이부프로펜;파마브롬', 'ENTP_NAME': '삼진제약(주)', 'CHART': '무색의 투명한 액이 든 분홍색의 투명한 타원형 연질캡슐', 'CHANGE_DATE': '2025-10-21', 'BAR_CODE': '8806478049402,8806478049419', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051259]이부프로펜|[M082487]파마브롬', '함량_원료성분원문': '총량 : 1캡슐850밀리그램|성분명 : 이부프로펜|분량 : 250.00|단위 : 밀리그램|규격 : BP|성분정보 : ;총량 : 1캡슐850밀리그램|성분명 : 파마브롬|분량 : 25.00|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1850', '수집URL': 'https://drug.hospitalk.net/item/201908295', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201908295', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201111097', 'ITEM_NAME': '게보린에스정(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아세트아미노펜;카페인무수물;제피아스코르브산', 'ENTP_NAME': '삼진제약(주)', 'CHART': '분홍색의 삼각형 정제', 'CHANGE_DATE': '2019-01-23', 'BAR_CODE': '8806478036808', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040353]아세트아미노펜|[M223183]카페인무수물|[M236913]제피아스코르브산', '함량_원료성분원문': '총량 : 이 약 1정(562mg) 중|성분명 : 아세트아미노펜|분량 : 320.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1정(562mg) 중|성분명 : 카페인무수물|분량 : 50.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1정(562mg) 중|성분명 : 제피아스코르브산|분량 : 51.55|단위 : 밀리그램|규격 : KPC|성분정보 : 아스코르빈산으로서 50mg', '함량_총량기준': '이 약 1정(562mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201111097', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201111097', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201200252', 'ITEM_NAME': '게보린에프정(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '리보플라빈3배산;티아민질산염3배산;이부프로펜', 'ENTP_NAME': '삼진제약(주)', 'CHART': '노란색의 삼각형 필름코팅정제', 'CHANGE_DATE': '2024-07-15', 'BAR_CODE': '8806478036907', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M100456]리보플라빈3배산|[M243282]티아민질산염3배산|[M051259]이부프로펜', '함량_원료성분원문': '총량 : 이 약 1정(573mg) 중|성분명 : 이부프로펜|분량 : 400.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1정(573mg) 중|성분명 : 티아민질산염3배산|분량 : 24.00|단위 : 밀리그램|규격 : KP|성분정보 : 티아민질산염으로서 8mg;총량 : 이 약 1정(573mg) 중|성분명 : 리보플라빈3배산|분량 : 12.00|단위 : 밀리그램|규격 : KP|성분정보 : 리보플라빈으로서 4mg', '함량_총량기준': '이 약 1정(573mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201200252', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201200252', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '197900277', 'ITEM_NAME': '게보린정(수출명:돌로린정)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아세트아미노펜;카페인무수물;이소프로필안티피린', 'ENTP_NAME': '삼진제약(주)', 'CHART': '홍색의 정제', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806478000403,8806478000410,8806478000427', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040353]아세트아미노펜|[M223183]카페인무수물|[M040499]이소프로필안티피린', '함량_원료성분원문': '총량 : 1정589.3밀리그램|성분명 : 아세트아미노펜|분량 : 300|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1정589.3밀리그램|성분명 : 카페인무수물|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정589.3밀리그램|성분명 : 이소프로필안티피린|분량 : 150|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1589.3', '수집URL': 'https://drug.hospitalk.net/item/197900277', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=197900277', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202401286', 'ITEM_NAME': '게보핏맥스플라스타(플루르비프로펜)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '플루르비프로펜', 'ENTP_NAME': '삼진제약(주)', 'CHART': '이 약은 무색 투명 또는 반투명의 점착성 물질을 지지체에 도포하고 고체면에 고체피복물을 덮은 첩부제이다.', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806478057704,8806478057711,8806478057728', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089049]플루르비프로펜', '함량_원료성분원문': '총량 : 1매|성분명 : 플루르비프로펜|분량 : 40.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1-C&H-Type', '수집URL': 'https://drug.hospitalk.net/item/202401286', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202401286', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202400559', 'ITEM_NAME': '게보핏스트롱카타플라스마(디클로페낙나트륨)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '디클로페낙나트륨', 'ENTP_NAME': '삼진제약(주)', 'CHART': '이 약은 흰색 또는 연한 노란색의 점착성 물질을 지지체 위에 도포하고 부직점착테이프로 고정시킨 후 고체피복물을 덮은 특유한 향기를 가진 카타플라스마제', 'CHANGE_DATE': '2025-01-08', 'BAR_CODE': '8806478057407,8806478057414', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050288]디클로페낙나트륨', '함량_원료성분원문': '총량 : 1매8.0그램|성분명 : 디클로페낙나트륨|분량 : 96.0|단위 : 밀리그램|규격 : EP|성분정보 :', '함량_총량기준': '18.0-6형(일체형)', '수집URL': 'https://drug.hospitalk.net/item/202400559', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202400559', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201708500', 'ITEM_NAME': '게보핏파워플라스타(디클로페낙나트륨)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '디클로페낙나트륨', 'ENTP_NAME': '삼진제약(주)', 'CHART': '무색 내지 미황색의 점착성 물질을 지지체에 도포하고 고체면에 고체피복물을 덮은 첩부제이다.', 'CHANGE_DATE': '2024-12-12', 'BAR_CODE': '8806478056608,8806478056615,8806478056622,8806478056639,8806478056646,8806478056707,8806478056714,8806478056721,8806478056738,8806478056745,8806478056806,8806478056813,8806478056820,8806798016108,8806798016115,8806798016122,8806798016139,8806798016146,8806798019604,8806798019611,8806798019628,8806798019635,8806798019642,8806798021300,8806798021317,8806798021324', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050288]디클로페낙나트륨|[M050288]디클로페낙나트륨|[M050288]디클로페낙나트륨|[M050288]디클로페낙나트륨|[M050288]디클로페낙나트륨|[M050288]디클로페낙나트륨', '함량_원료성분원문': '총량 : 제 1형 1매(7cm×10cm, 70cm2, 2.0g)중|성분명 : 디클로페낙나트륨|분량 : 15.00|단위 : 밀리그램|규격 : EP|성분정보 : ;총량 : 제 2형 1매(7cm×10cm, 70cm2, 2.0g)중|성분명 : 디클로페낙나트륨|분량 : 15.00|단위 : 밀리그램|규격 : EP|성분정보 : ;총량 : 제 3형 1매(7cm×14cm, 98cm2, 2.8g)중|성분명 : 디클로페낙나트륨|분량 : 21.00|단위 : 밀리그램|규격 : EP|성분정보 : ;총량 : 제 4형 1매(7cm×14cm, 98cm2, 2.8g)중|성분명 : 디클로페낙나트륨|분량 : 21.00|단위 : 밀리그램|규격 : EP|성분정보 : ;총량 : 제 5형 1매(7cm×15cm, 105cm², 3.0g)중|성분명 : 디클로페낙나트륨|분량 : 22.50|단위 : 밀리그램|규격 : EP|성분정보 : ;총량 : 제 6형 1매(7cm×15cm, 105cm², 3.0g)중|성분명 : 디클로페낙나트륨|분량 : 22.50|단위 : 밀리그램|규격 : EP|성분정보 :', '함량_총량기준': '제 1형 1매(7cm×10cm, 70cm2, 2.0g)중/제 2형 1매(7cm×10cm, 70cm2, 2.0g)중/제 3형 1매(7cm×14cm, 98cm2, 2.8g)중/제 4형 1매(7cm×14cm, 98cm2, 2.8g)중/제 5형 1매(7cm×15cm, 105cm², 3.0g)중/제 6형 1매(7cm×15cm, 105cm², 3.0g)중', '수집URL': 'https://drug.hospitalk.net/item/201708500', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201708500', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201310271', 'ITEM_NAME': '게이트정(알마게이트)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '알마게이트', 'ENTP_NAME': '오스틴제약(주)', 'CHART': '흰색의 타원형 정제', 'CHANGE_DATE': '2026-08-06', 'BAR_CODE': '8806543048309,8806543048316', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081294]알마게이트', '함량_원료성분원문': '총량 : 1정(535mg) 중|성분명 : 알마게이트|분량 : 500|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정(535mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201310271', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201310271', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202602669', 'ITEM_NAME': '겐타스크림', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '베타메타손발레레이트;겐타마이신황산염', 'ENTP_NAME': '(주)시어스제약', 'CHART': '흰색의 크림제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806890020003,8806890020010', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223043]베타메타손발레레이트|[M202821]겐타마이신황산염', '함량_원료성분원문': '총량 : 1그램|성분명 : 베타메타손발레레이트|분량 : 0.61|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램|성분명 : 겐타마이신황산염|분량 : 1|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/202602669', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202602669', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201400916', 'ITEM_NAME': '겔비스톤현탁액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '알긴산나트륨;탄산수소나트륨;침강탄산칼슘', 'ENTP_NAME': '(주)텔콘알에프제약', 'CHART': '알루미늄호일 파우치에 든 향기가 있는 미황색의 현탁액', 'CHANGE_DATE': '2024-06-14', 'BAR_CODE': '8806255000206,8806255000213,8806255000220,8806255000237,8806255000244,8806255000251,8806255000268,8806255000275,8806255000282,8806255000299,8806255000718,8806255000725,8806255000732,8806255000749,8806255000756,8806255000763,8806255000770', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040385]알긴산나트륨|[M040631]탄산수소나트륨|[M040634]침강탄산칼슘', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 알긴산나트륨|분량 : 5.0|단위 : 그램|규격 : NF|성분정보 : 건조물로서 4.25그램;총량 : 100밀리리터|성분명 : 탄산수소나트륨|분량 : 2.13|단위 : 그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 침강탄산칼슘|분량 : 3.25|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/201400916', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201400916', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202601555', 'ITEM_NAME': '겔포스더블액션정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '파모티딘;수산화마그네슘;침강탄산칼슘', 'ENTP_NAME': '(주)보령', 'CHART': '연두색의 장방형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806419089900,8806419089917', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081653]파모티딘|[M040306]수산화마그네슘|[M040634]침강탄산칼슘', '함량_원료성분원문': '총량 : 1정1,230밀리그램|성분명 : 파모티딘|분량 : 10|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1정1,230밀리그램|성분명 : 수산화마그네슘|분량 : 165|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정1,230밀리그램|성분명 : 침강탄산칼슘|분량 : 800|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '11,230', '수집URL': 'https://drug.hospitalk.net/item/202601555', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202601555', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201708580', 'ITEM_NAME': '겔포스엘현탁액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': 'DL-카르니틴염산염;시메티콘;수산화마그네슘;인산알루미늄겔', 'ENTP_NAME': '(주)보령', 'CHART': '알루미늄 필름에 들어있는 흰색~담백색의 현탁액', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806419066802,8806419066819,8806419066826,8806419066833,8806419066840', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M246203]DL-카르니틴염산염|[M223083]시메티콘|[M040306]수산화마그네슘|[M051477]인산알루미늄겔', '함량_원료성분원문': '총량 : 100그램|성분명 : 인산알루미늄겔|분량 : 12.5|단위 : 그램|규격 : EP|성분정보 : ;총량 : 100그램|성분명 : 수산화마그네슘|분량 : 2|단위 : 그램|규격 : KP|성분정보 : ;총량 : 100그램|성분명 : 시메티콘|분량 : 0.225|단위 : 그램|규격 : USP|성분정보 : ;총량 : 100그램|성분명 : DL-카르니틴염산염|분량 : 0.75|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/201708580', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201708580', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199400883', 'ITEM_NAME': '겔포스엠현탁액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '인산알루미늄겔;시메티콘;수산화마그네슘', 'ENTP_NAME': '(주)보령', 'CHART': '이 약은 흰색-담백색의 겔로서 물로 희석하면 곧 균질의 현탁액이 된 다음 서서히 침강한다', 'CHANGE_DATE': '2024-11-06', 'BAR_CODE': '8806419000400,8806419000417,8806419000424,8806419000431,8806419000448,8806419000455,8806419000462,8806419000479,8806419000486,8806419000493', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051477]인산알루미늄겔|[M223083]시메티콘|[M040306]수산화마그네슘|[M051477]인산알루미늄겔|[M223083]시메티콘|[M040306]수산화마그네슘|[M051477]인산알루미늄겔|[M223083]시메티콘|[M040306]수산화마그네슘|[M051477]인산알루미늄겔|[M223083]시메티콘|[M040306]수산화마그네슘', '함량_원료성분원문': '총량 : 100그램|성분명 : 인산알루미늄겔|분량 : 61.9|단위 : 그램|규격 : EP|성분정보 : 인산알루미늄으로서 12.38g;총량 : 100그램|성분명 : 수산화마그네슘|분량 : 2.0|단위 : 그램|규격 : KP|성분정보 : 마그네슘으로서 833.5mg;총량 : 100그램|성분명 : 시메티콘|분량 : 0.2|단위 : 그램|규격 : USP|성분정보 : ;총량 : 100그램|성분명 : 인산알루미늄겔|분량 : 61.9|단위 : 그램|규격 : EP|성분정보 : 인산알루미늄으로서 12.38g;총량 : 100그램|성분명 : 수산화마그네슘|분량 : 2.0|단위 : 그램|규격 : KP|성분정보 : 마그네슘으로서 833.5mg;총량 : 100그램|성분명 : 시메티콘|분량 : 0.2|단위 : 그램|규격 : USP|성분정보 : ;총량 : 100그램|성분명 : 인산알루미늄겔|분량 : 61.9|단위 : 그램|규격 : EP|성분정보 : 인산알루미늄으로서 12.38g;총량 : 100그램|성분명 : 수산화마그네슘|분량 : 2.0|단위 : 그램|규격 : KP|성분정보 : 마그네슘으로서 833.5mg;총량 : 100그램|성분명 : 시메티콘|분량 : 0.2|단위 : 그램|규격 : USP|성분정보 : ;총량 : 100그램|성분명 : 인산알루미늄겔|분량 : 61.9|단위 : 그램|규격 : EP|성분정보 : 인산알루미늄으로서 12.38g;총량 : 100그램|성분명 : 수산화마그네슘|분량 : 2.0|단위 : 그램|규격 : KP|성분정보 : 마그네슘으로서 833.5mg;총량 : 100그램|성분명 : 시메티콘|분량 : 0.2|단위 : 그램|규격 : USP|성분정보 :', '함량_총량기준': '100-제품1(오렌지향)/100-제품2(파인애플향)/100-제품3(딸기향)/100-제품4(민트향)', '수집URL': 'https://drug.hospitalk.net/item/199400883', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199400883', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '197400207', 'ITEM_NAME': '겔포스현탁액(인산알루미늄겔)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '인산알루미늄겔;콜로이드성인산알루미늄', 'ENTP_NAME': '(주)보령', 'CHART': '흰색 ~ 연한 흰색의 겔로서 녹이면 곧 균질의 현탁액이 된 다음 서서히 침강한다', 'CHANGE_DATE': '2015-01-28', 'BAR_CODE': '8806419000103,8806419000110,8806419000127,8806419000134,8806419000141,8806419000158,8806419000165,8806419000172,8806419000189,8806419000196,8806419000219,8806419000226,8806419000233,8806419000240,8806419000257,8806419000271,8806419000288,8806419000295', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051477]인산알루미늄겔|[M088813]콜로이드성인산알루미늄', '함량_원료성분원문': '총량 : 100그램|성분명 : 인산알루미늄겔|분량 : 61.9|단위 : 그램|규격 : EP|성분정보 : AlPO4 로서 12.38g;총량 : 100그램|성분명 : 콜로이드성인산알루미늄|분량 : 55|단위 : 그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '100/100-수출용', '수집URL': 'https://drug.hospitalk.net/item/197400207', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=197400207', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199702146', 'ITEM_NAME': '겟투겔(케토프로펜)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '케토프로펜', 'ENTP_NAME': '한국넬슨제약(주)', 'CHART': '무색투명한 점액성의 겔제', 'CHANGE_DATE': '2013-01-02', 'BAR_CODE': '8806567000208,8806567000215,8806567000222', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051464]케토프로펜', '함량_원료성분원문': '총량 : 1그램|성분명 : 케토프로펜|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/199702146', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199702146', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202502584', 'ITEM_NAME': '경남갈근탕액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건강;대추;마황;갈근;감초;계지;작약', 'ENTP_NAME': '경남제약(주)', 'CHART': '흑갈색의 액제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806476040906,8806476040913,8806476040920', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040007]건강|[M040071]대추|[M040135]마황|[M040004]갈근|[M040006]감초|[M050037]계지|[M040523]작약', '함량_원료성분원문': '총량 : 1포75밀리리터|성분명 : 작약|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포75밀리리터|성분명 : 계지|분량 : 1.00|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포75밀리리터|성분명 : 감초|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포75밀리리터|성분명 : 갈근|분량 : 2.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포75밀리리터|성분명 : 마황|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포75밀리리터|성분명 : 대추|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포75밀리리터|성분명 : 건강|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '175', '수집URL': 'https://drug.hospitalk.net/item/202502584', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202502584', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201804969', 'ITEM_NAME': '경남경옥고', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '꿀;복령;인삼;생지황즙', 'ENTP_NAME': '경남제약(주)', 'CHART': '알루미늄 스틱포에 충전된 흑갈색의 점도가 있는 연조엑스제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806476035704,8806476035711,8806476035728', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M200168]꿀|[M040225]복령|[M040213]인삼|[M082091]생지황즙', '함량_원료성분원문': '총량 : 100g 중|성분명 : 생지황즙|분량 : 39.9|단위 : 그램|규격 : 별규|성분정보 : ;총량 : 100g 중|성분명 : 인삼|분량 : 6.2|단위 : 그램|규격 : KP|성분정보 : ;총량 : 100g 중|성분명 : 복령|분량 : 12.4|단위 : 그램|규격 : KP|성분정보 : ;총량 : 100g 중|성분명 : 꿀|분량 : 41.5|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '100g 중', '수집URL': 'https://drug.hospitalk.net/item/201804969', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201804969', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200501415', 'ITEM_NAME': '경남그린웰연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '셀레늄가루 0.1%;산화아연;피리독신염산염;리보플라빈;티아민질산염;유비데카레논;β-카로틴현탁액30%;아스코르브산;토코페롤아세테이트', 'ENTP_NAME': '경남제약(주)', 'CHART': '적갈색의 내용물을 함유한 암적색의 장방형 연질캡슐', 'CHANGE_DATE': '2026-09-01', 'BAR_CODE': '8806476000207,8806476000214,8806476000221,8806476000238,8806476000245', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M248796]셀레늄가루 0.1%|[M243785]산화아연|[M204304]피리독신염산염|[M040133]리보플라빈|[M223262]티아민질산염|[M051233]유비데카레논|[M250857]β-카로틴현탁액30%|[M258994]아스코르브산|[M223240]토코페롤아세테이트', '함량_원료성분원문': '총량 : 1캡슐(1,576 mg) 중|성분명 : 토코페롤아세테이트|분량 : 200|단위 : 밀리그램|규격 : KP|성분정보 : 비타민E로서 200I.U.;총량 : 1캡슐(1,576 mg) 중|성분명 : 아스코르브산|분량 : 450|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,576 mg) 중|성분명 : β-카로틴현탁액30%|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : 베타카로틴으로서 3mg;총량 : 1캡슐(1,576 mg) 중|성분명 : 유비데카레논|분량 : 5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,576 mg) 중|성분명 : 티아민질산염|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,576 mg) 중|성분명 : 리보플라빈|분량 : 6|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,576 mg) 중|성분명 : 피리독신염산염|분량 : 25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,576 mg) 중|성분명 : 산화아연|분량 : 17.43|단위 : 밀리그램|규격 : KP|성분정보 : 아연으로서 14mg;총량 : 1캡슐(1,576 mg) 중|성분명 : 셀레늄가루 0.1%|분량 : 25|단위 : 밀리그램|규격 : KP|성분정보 : 셀레늄으로서 25μg', '함량_총량기준': '1캡슐(1,576 mg) 중', '수집URL': 'https://drug.hospitalk.net/item/200501415', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200501415', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201403474', 'ITEM_NAME': '경남나프록센연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '나프록센', 'ENTP_NAME': '경남제약(주)', 'CHART': '무색의 투명한 액이 든 청록색의 투명한 타원형 연질캡슐', 'CHANGE_DATE': '2025-02-03', 'BAR_CODE': '8806476032703,8806476032710', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050116]나프록센', '함량_원료성분원문': '총량 : 1캡슐1,080밀리그램|성분명 : 나프록센|분량 : 250.00|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '11,080', '수집URL': 'https://drug.hospitalk.net/item/201403474', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201403474', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201307766', 'ITEM_NAME': '경남데일리디츄어블정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '콜레칼시페롤과립;유비데카레논', 'ENTP_NAME': '경남제약(주)', 'CHART': '연노란색 원형 츄어블정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806476031904,8806476031911', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M099907]콜레칼시페롤과립|[M051233]유비데카레논', '함량_원료성분원문': '총량 : 1정(699mg) 중|성분명 : 콜레칼시페롤과립|분량 : 5|단위 : 밀리그램|규격 : 별규|성분정보 : 비타민D로서500I.U;총량 : 1정(699mg) 중|성분명 : 유비데카레논|분량 : 2|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정(699mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201307766', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201307766', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200904353', 'ITEM_NAME': '경남비타민씨정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아스코르브산97%과립', 'ENTP_NAME': '경남제약(주)', 'CHART': '흰색의 장방형 정제', 'CHANGE_DATE': '2014-08-07', 'BAR_CODE': '8806476017502,8806476017519,8806476017526,8806476017533,8806476017540,8806476017557,8806476017564,8806476017571', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M227509]아스코르브산97%과립', '함량_원료성분원문': '총량 : 1정 (1,185.0mg) 중|성분명 : 아스코르브산97%과립|분량 : 1031|단위 : 밀리그램|규격 : 별규|성분정보 : 비타민C(아스코르브산)로서 1000mg', '함량_총량기준': '1정 (1,185.0mg) 중', '수집URL': 'https://drug.hospitalk.net/item/200904353', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200904353', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201801844', 'ITEM_NAME': '경남생맥산액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '인삼;오미자;맥문동', 'ENTP_NAME': '경남제약(주)', 'CHART': '불투명한 알루미늄파우치 또는 갈색유리병에 들어있는 생약의 향취가 있는 갈색의 액제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806476035209,8806476035216,8806476035223', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040213]인삼|[M040445]오미자|[M040139]맥문동', '함량_원료성분원문': '총량 : 1회 용량(100ml) 중 |성분명 : 인삼|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(100ml) 중 |성분명 : 오미자|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(100ml) 중 |성분명 : 맥문동|분량 : 2.5|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1회 용량(100ml) 중', '수집URL': 'https://drug.hospitalk.net/item/201801844', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201801844', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202201616', 'ITEM_NAME': '경남세티리진정(세티리진염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '세티리진염산염', 'ENTP_NAME': '경남제약(주)', 'CHART': '흰색의 장방형 필름코팅정', 'CHANGE_DATE': '2026-01-07', 'BAR_CODE': '8806476038101,8806476038118,8806476038125', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M222857]세티리진염산염', '함량_원료성분원문': '총량 : 1정148.5밀리그램|성분명 : 세티리진염산염|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1148.5', '수집URL': 'https://drug.hospitalk.net/item/202201616', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202201616', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202602085', 'ITEM_NAME': '경남아시클로버크림', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아시클로버', 'ENTP_NAME': '경남제약(주)', 'CHART': '전질이 고른 흰색의 크림제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806476041903,8806476041910', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081569]아시클로버', '함량_원료성분원문': '총량 : 1그램|성분명 : 아시클로버|분량 : 50|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/202602085', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202602085', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201907745', 'ITEM_NAME': '경남우황청심원액(사향대체물질L-무스콘함유)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': 'l-무스콘;용뇌;백렴;건강;인삼;포황;신곡;대두황권;육계;아교;작약;영양각;우황;감초;산약;맥문동;황금;당귀;방풍;백출;시호;복령;길경;행인;천궁', 'ENTP_NAME': '경남제약(주)', 'CHART': '특이한 방향성이 있는 갈색의 불투명한 액제', 'CHANGE_DATE': '2020-10-07', 'BAR_CODE': '8806476036305,8806476036312', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M251442]l-무스콘|[M051197]용뇌|[M050541]백렴|[M040007]건강|[M051291]인삼|[M090765]포황|[M050891]신곡|[M050191]대두황권|[M050036]육계|[M050905]아교|[M040523]작약|[M051133]영양각|[M040478]우황|[M040006]감초|[M040258]산약|[M040139]맥문동|[M040789]황금|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040336]시호|[M040225]복령|[M040048]길경|[M040769]행인|[M040550]천궁', '함량_원료성분원문': '총량 : 1병50밀리리터|성분명 : 산약|분량 : 282|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 맥문동|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 황금|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 당귀|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 방풍|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 백출|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 시호|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 복령|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 길경|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 행인|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 천궁|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 감초|분량 : 202|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 우황|분량 : 14|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 영양각|분량 : 35|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : l-무스콘|분량 : 75|단위 : 마이크로그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 용뇌|분량 : 41|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 백렴|분량 : 30|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 건강|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 인삼|분량 : 97|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 포황|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 신곡|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 대두황권|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 육계|분량 : 70|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 아교|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 작약|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '150', '수집URL': 'https://drug.hospitalk.net/item/201907745', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201907745', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201907948', 'ITEM_NAME': '경남우황청심원현탁액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건강;백렴;용뇌;사향;인삼;포황;신곡;대두황권;육계;아교;작약;영양각;우황;감초;산약;맥문동;황금;당귀;방풍;백출;시호;복령;길경;행인;천궁', 'ENTP_NAME': '경남제약(주)', 'CHART': '갈색유리병에 든 특이한 방향성이 있는 갈색의 불투명한 현탁제', 'CHANGE_DATE': '2020-10-14', 'BAR_CODE': '8806476036404,8806476036411', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040007]건강|[M050541]백렴|[M051197]용뇌|[M040253]사향|[M051291]인삼|[M090765]포황|[M050891]신곡|[M050191]대두황권|[M050036]육계|[M050905]아교|[M040523]작약|[M051133]영양각|[M040478]우황|[M040006]감초|[M040258]산약|[M040139]맥문동|[M040789]황금|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040336]시호|[M040225]복령|[M040048]길경|[M040769]행인|[M040550]천궁', '함량_원료성분원문': '총량 : 1병50밀리리터|성분명 : 산약|분량 : 282|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 맥문동|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 황금|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 당귀|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 방풍|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 백출|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 시호|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 복령|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 길경|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 행인|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 천궁|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 감초|분량 : 202|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 우황|분량 : 14|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 영양각|분량 : 35|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 백렴|분량 : 30|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 건강|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 인삼|분량 : 97|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 포황|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 신곡|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 대두황권|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 육계|분량 : 70|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 아교|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 작약|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '150', '수집URL': 'https://drug.hospitalk.net/item/201907948', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201907948', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202400850', 'ITEM_NAME': '경남티어앤톡모이스처점안액1.0%(카르복시메틸셀룰로오스나트륨)(1회용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '카르복시메틸셀룰로오스나트륨', 'ENTP_NAME': '경남제약(주)', 'CHART': '무색 투명한 플라스틱 용기에 든 무색 내지 미황색의 맑은 점안액', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806476039405,8806476039412,8806476039429', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M244062]카르복시메틸셀룰로오스나트륨', '함량_원료성분원문': '총량 : 1밀리리터|성분명 : 카르복시메틸셀룰로오스나트륨|분량 : 10.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/202400850', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202400850', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201906917', 'ITEM_NAME': '경남티어앤톡점안액(트레할로스수화물)(1회용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '트레할로스수화물', 'ENTP_NAME': '경남제약(주)', 'CHART': '무색 투명한 액이 무색 투명한 플라스틱 용기에 든 점안액', 'CHANGE_DATE': '2025-03-26', 'BAR_CODE': '8806476036206,8806476036213,8806476036220,8806476036237,8806476038309,8806476038316,8806476038323,8806476038330', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M260745]트레할로스수화물', '함량_원료성분원문': '총량 : 1밀리리터|성분명 : 트레할로스수화물|분량 : 33.16|단위 : 밀리그램|규격 : EP|성분정보 : 트레할로스로서 30밀리그램', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/201906917', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201906917', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202602438', 'ITEM_NAME': '경남피록시캄겔', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '피록시캄', 'ENTP_NAME': '경남제약(주)', 'CHART': '연노랑색의 투명한 겔제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806476042207,8806476042214', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M071634]피록시캄', '함량_원료성분원문': '총량 : 1그램|성분명 : 피록시캄|분량 : 5.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/202602438', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202602438', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201309112', 'ITEM_NAME': '경동아스피린장용정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아스피린', 'ENTP_NAME': '경동제약(주)', 'CHART': '흰색의 원형 장용성 필름코팅정제', 'CHANGE_DATE': '2026-08-03', 'BAR_CODE': '8806481033207,8806481033214,8806481033221,8806481033238', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040355]아스피린', '함량_원료성분원문': '총량 : 1정169밀리그램|성분명 : 아스피린|분량 : 100.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1169', '수집URL': 'https://drug.hospitalk.net/item/201309112', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201309112', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202106054', 'ITEM_NAME': '경동파니틴정10밀리그램(파모티딘)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '파모티딘', 'ENTP_NAME': '경동제약(주)', 'CHART': '녹색의 원형 필름코팅정', 'CHANGE_DATE': '2024-11-07', 'BAR_CODE': '8806481048706,8806481048713', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081653]파모티딘', '함량_원료성분원문': '총량 : 1정100밀리그램|성분명 : 파모티딘|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1100', '수집URL': 'https://drug.hospitalk.net/item/202106054', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202106054', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202107682', 'ITEM_NAME': '경동판테놀연고(덱스판테놀)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '덱스판테놀', 'ENTP_NAME': '경동제약(주)', 'CHART': '흰색의 연고제', 'CHANGE_DATE': '2025-05-12', 'BAR_CODE': '8806481047303,8806481047310', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M278679]덱스판테놀', '함량_원료성분원문': '총량 : 1그램그램|성분명 : 덱스판테놀|분량 : 50.0|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/202107682', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202107682', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005591', 'ITEM_NAME': '경방가미소요산산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '박하엑스산;감초엑스산;목단피엑스산;치자엑스산;시호엑스산;백출엑스산;복령엑스산;작약엑스산;당귀엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613000909,8806613000916,8806613000923,8806613000930,8806613000947,8806613000954,8806613000961,8806613000978,8806613040301,8806613040318,8806613040325,8806613040332,8806613040349,8806613040356', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089555]박하엑스산|[M082727]감초엑스산|[M089521]목단피엑스산|[M089503]치자엑스산|[M089498]시호엑스산|[M089527]백출엑스산|[M089528]복령엑스산|[M090093]작약엑스산|[M089119]당귀엑스산', '함량_원료성분원문': '총량 : 1회 용량 (2.85그램) 중|성분명 : 당귀엑스산|분량 : 0.46|단위 : 그램|규격 : 생규|성분정보 : 당귀로서 1.25g;총량 : 1회 용량 (2.85그램) 중|성분명 : 작약엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 작약으로서 1.25g;총량 : 1회 용량 (2.85그램) 중|성분명 : 복령엑스산|분량 : 0.03|단위 : 그램|규격 : 생규|성분정보 : 복령으로서 1.25g;총량 : 1회 용량 (2.85그램) 중|성분명 : 백출엑스산|분량 : 0.46|단위 : 그램|규격 : 생규|성분정보 : 백출로서 1.25g;총량 : 1회 용량 (2.85그램) 중|성분명 : 시호엑스산|분량 : 0.21|단위 : 그램|규격 : 생규|성분정보 : 시호로서 1.25g;총량 : 1회 용량 (2.85그램) 중|성분명 : 치자엑스산|분량 : 0.44|단위 : 그램|규격 : 생규|성분정보 : 치자로서 1.25g;총량 : 1회 용량 (2.85그램) 중|성분명 : 목단피엑스산|분량 : 0.45|단위 : 그램|규격 : 생규|성분정보 : 목단피로서 1.25g;총량 : 1회 용량 (2.85그램) 중|성분명 : 감초엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 감초로서 1.25g;총량 : 1회 용량 (2.85그램) 중|성분명 : 박하엑스산|분량 : 0.12|단위 : 그램|규격 : 생규|성분정보 : 박하로서 0.63g', '함량_총량기준': '1회 용량 (2.85그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005591', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005591', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005799', 'ITEM_NAME': '경방가미소요산엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건강;감초;치자;목단피;시호;백출;복령;작약;박하;당귀', 'ENTP_NAME': '경방신약(주)', 'CHART': '회갈색의 과립제', 'CHANGE_DATE': '2020-09-25', 'BAR_CODE': '8806613001005,8806613001012', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040007]건강|[M040006]감초|[M040564]치자|[M040185]목단피|[M040336]시호|[M040214]백출|[M040225]복령|[M040523]작약|[M040198]박하|[M040070]당귀', '함량_원료성분원문': '총량 : 1회 용량(2.5 g) 중|성분명 : 당귀|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5 g) 중|성분명 : 박하|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5 g) 중|성분명 : 작약|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : 패오니플로린으로서 23밀리그램;총량 : 1회 용량(2.5 g) 중|성분명 : 복령|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5 g) 중|성분명 : 백출|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5 g) 중|성분명 : 시호|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5 g) 중|성분명 : 목단피|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5 g) 중|성분명 : 치자|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : 게니포시드로서 20.1밀리그램;총량 : 1회 용량(2.5 g) 중|성분명 : 감초|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : 글리시리진산으로서 16.75밀리그램;총량 : 1회 용량(2.5 g) 중|성분명 : 건강|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1회 용량(2.5 g) 중', '수집URL': 'https://drug.hospitalk.net/item/200005799', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005799', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201908041', 'ITEM_NAME': '경방가미소요산연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '박하연조엑스(3.2~4.0→1);감초연조엑스(2.1~2.5→1);목단피연조엑스(2.8~3.4→1);치자연조엑스(2.1~2.6→1);시호 연조엑스(3.6~4.4→1);백출연조엑스(2.8~3.4→1);복령연조엑스(5.8~7.8→1);작약연조엑스(2.8~3.4→1);당귀연조엑스(2.8~3.4→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806613053707,8806613053714,8806613053721,8806613053738', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268536]박하연조엑스(3.2~4.0→1)|[M268186]감초연조엑스(2.1~2.5→1)|[M270589]목단피연조엑스(2.8~3.4→1)|[M269893]치자연조엑스(2.1~2.6→1)|[M117858]시호 연조엑스(3.6~4.4→1)|[M268184]백출연조엑스(2.8~3.4→1)|[M268326]복령연조엑스(5.8~7.8→1)|[M268187]작약연조엑스(2.8~3.4→1)|[M268188]당귀연조엑스(2.8~3.4→1)', '함량_원료성분원문': '총량 : 1회 용량(10g/포)|성분명 : 당귀연조엑스(2.8~3.4→1)|분량 : 412.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)|성분명 : 작약연조엑스(2.8~3.4→1)|분량 : 412.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)|성분명 : 복령연조엑스(5.8~7.8→1)|분량 : 187.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)|성분명 : 백출연조엑스(2.8~3.4→1)|분량 : 412.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)|성분명 : 시호 연조엑스(3.6~4.4→1)|분량 : 312.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)|성분명 : 치자연조엑스(2.1~2.6→1)|분량 : 537.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)|성분명 : 목단피연조엑스(2.8~3.4→1)|분량 : 412.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)|성분명 : 감초연조엑스(2.1~2.5→1)|분량 : 550.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)|성분명 : 박하연조엑스(3.2~4.0→1)|분량 : 176.4|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1회 용량(10g/포)', '수집URL': 'https://drug.hospitalk.net/item/201908041', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201908041', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005592', 'ITEM_NAME': '경방갈근탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대추엑스산;생강엑스산;감초엑스산;계지엑스산;작약엑스산;마황엑스산;갈근엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613001203,8806613001210,8806613001227,8806613001234,8806613001241,8806613001258,8806613001265,8806613040400,8806613040417,8806613040424,8806613040431,8806613040448,8806613040455', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089515]대추엑스산|[M089512]생강엑스산|[M082727]감초엑스산|[M089525]계지엑스산|[M090093]작약엑스산|[M089573]마황엑스산|[M089599]갈근엑스산', '함량_원료성분원문': '총량 : 1회 용량(3.28그램) 중|성분명 : 갈근엑스산|분량 : 1.69|단위 : 그램|규격 : 생규|성분정보 : 갈근으로서 3.75 g;총량 : 1회 용량(3.28그램) 중|성분명 : 마황엑스산|분량 : 0.40|단위 : 그램|규격 : 생규|성분정보 : 마황으로서 2.50 g;총량 : 1회 용량(3.28그램) 중|성분명 : 작약엑스산|분량 : 0.51|단위 : 그램|규격 : 생규|성분정보 : 작약으로서 1.88 g;총량 : 1회 용량(3.28그램) 중|성분명 : 계지엑스산|분량 : 0.04|단위 : 그램|규격 : 생규|성분정보 : 계지로서 1.25 g;총량 : 1회 용량(3.28그램) 중|성분명 : 감초엑스산|분량 : 0.27|단위 : 그램|규격 : 생규|성분정보 : 감초로서 1.00 g;총량 : 1회 용량(3.28그램) 중|성분명 : 생강엑스산|분량 : 0.03|단위 : 그램|규격 : 생규|성분정보 : 생강으로서 0.50 g;총량 : 1회 용량(3.28그램) 중|성분명 : 대추엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 대추로서 0.67 g', '함량_총량기준': '1회 용량(3.28그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005592', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005592', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200711872', 'ITEM_NAME': '경방갈근탕액(갈근탕액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건강;대추;마황;갈근;감초;계지;작약', 'ENTP_NAME': '경방신약(주)', 'CHART': '흑갈색의 액제', 'CHANGE_DATE': '2022-09-20', 'BAR_CODE': '8806613001302,8806613001319', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040007]건강|[M040071]대추|[M040135]마황|[M040004]갈근|[M040006]감초|[M050037]계지|[M040523]작약', '함량_원료성분원문': '총량 : 1포(75밀리리터) 중|성분명 : 작약|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(75밀리리터) 중|성분명 : 계지|분량 : 1.00|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포(75밀리리터) 중|성분명 : 감초|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(75밀리리터) 중|성분명 : 갈근|분량 : 2.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(75밀리리터) 중|성분명 : 마황|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(75밀리리터) 중|성분명 : 대추|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(75밀리리터) 중|성분명 : 건강|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1포(75밀리리터) 중', '수집URL': 'https://drug.hospitalk.net/item/200711872', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200711872', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201803949', 'ITEM_NAME': '경방갈근탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대추연조엑스(1.8~2.2→1);생강연조엑스(5.1~6.9→1);감초연조엑스(2.1∼2.5→1);계지연조엑스(7.6～11.4→1);작약연조엑스(2.8~3.4→1);마황연조엑스(3.8∼5.1→1);갈근연조엑스(2.5~3.1→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2020-07-27', 'BAR_CODE': '8806613050102,8806613050119,8806613050126', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M266595]대추연조엑스(1.8~2.2→1)|[M268065]생강연조엑스(5.1~6.9→1)|[M268064]감초연조엑스(2.1∼2.5→1)|[M268322]계지연조엑스(7.6～11.4→1)|[M268068]작약연조엑스(2.8~3.4→1)|[M268323]마황연조엑스(3.8∼5.1→1)|[M266589]갈근연조엑스(2.5~3.1→1)', '함량_원료성분원문': '총량 : 1회용량(10g/포) 중|성분명 : 갈근연조엑스(2.5~3.1→1)|분량 : 1,350.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회용량(10g/포) 중|성분명 : 마황연조엑스(3.8∼5.1→1)|분량 : 575.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회용량(10g/포) 중|성분명 : 작약연조엑스(2.8~3.4→1)|분량 : 620.4|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회용량(10g/포) 중|성분명 : 계지연조엑스(7.6～11.4→1)|분량 : 137.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회용량(10g/포) 중|성분명 : 감초연조엑스(2.1∼2.5→1)|분량 : 440.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회용량(10g/포) 중|성분명 : 생강연조엑스(5.1~6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회용량(10g/포) 중|성분명 : 대추연조엑스(1.8~2.2→1)|분량 : 341.7|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회용량(10g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/201803949', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201803949', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201604490', 'ITEM_NAME': '경방갈근탕정(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대추연조엑스(1.8∼2.2→1);생강연조엑스(5.1～6.9→1);감초연조엑스(2.1∼2.5→1);계지연조엑스(7.6～11.4→1);작약연조엑스(2.8～3.4→1);마황연조엑스(3.8∼5.1→1);갈근연조엑스(2.5∼3.1→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '적갈색의 장방형 필름코팅정', 'CHANGE_DATE': '2026-10-23', 'BAR_CODE': '8806613046907,8806613046914,8806613046921,8806613046938', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M280340]대추연조엑스(1.8∼2.2→1)|[M280339]생강연조엑스(5.1～6.9→1)|[M280338]감초연조엑스(2.1∼2.5→1)|[M280337]계지연조엑스(7.6～11.4→1)|[M280336]작약연조엑스(2.8～3.4→1)|[M280335]마황연조엑스(3.8∼5.1→1)|[M280334]갈근연조엑스(2.5∼3.1→1)', '함량_원료성분원문': '총량 : 1회용량(640 mg/정 x 4정)|성분명 : 갈근연조엑스(2.5∼3.1→1)|분량 : 1350.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회용량(640 mg/정 x 4정)|성분명 : 마황연조엑스(3.8∼5.1→1)|분량 : 575.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회용량(640 mg/정 x 4정)|성분명 : 작약연조엑스(2.8～3.4→1)|분량 : 620.4|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회용량(640 mg/정 x 4정)|성분명 : 계지연조엑스(7.6～11.4→1)|분량 : 137.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회용량(640 mg/정 x 4정)|성분명 : 감초연조엑스(2.1∼2.5→1)|분량 : 440.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회용량(640 mg/정 x 4정)|성분명 : 생강연조엑스(5.1～6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회용량(640 mg/정 x 4정)|성분명 : 대추연조엑스(1.8∼2.2→1)|분량 : 341.7|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회용량(640 mg/정 x 4정)', '수집URL': 'https://drug.hospitalk.net/item/201604490', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201604490', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005593', 'ITEM_NAME': '경방갈근해기탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '길경엑스산;백지엑스산;승마엑스산;작약엑스산;석고;강활엑스산;황금엑스산;갈근엑스산;감초엑스산;생강엑스산;대추엑스산;시호엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613001401,8806613001418,8806613001425,8806613001432,8806613001449,8806613001456,8806613001463,8806613040509,8806613040516,8806613040523,8806613040530,8806613040547,8806613040554,8806613040561', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M084832]길경엑스산|[M089600]백지엑스산|[M089520]승마엑스산|[M090093]작약엑스산|[M040279]석고|[M089546]강활엑스산|[M089535]황금엑스산|[M089599]갈근엑스산|[M082727]감초엑스산|[M089512]생강엑스산|[M089515]대추엑스산|[M089498]시호엑스산', '함량_원료성분원문': '총량 : 1회 용량(5.00그램) 중|성분명 : 갈근엑스산|분량 : 0.56|단위 : 그램|규격 : 생규|성분정보 : 갈근으로서 1.25g;총량 : 1회 용량(5.00그램) 중|성분명 : 감초엑스산|분량 : 0.17|단위 : 그램|규격 : 생규|성분정보 : 감초으로서 0.63g;총량 : 1회 용량(5.00그램) 중|성분명 : 생강엑스산|분량 : 0.03|단위 : 그램|규격 : 생규|성분정보 : 생강으로서 0.50g;총량 : 1회 용량(5.00그램) 중|성분명 : 대추엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 대추로서 0.67g;총량 : 1회 용량(5.00그램) 중|성분명 : 시호엑스산|분량 : 0.21|단위 : 그램|규격 : 생규|성분정보 : 시호로서 1.25g;총량 : 1회 용량(5.00그램) 중|성분명 : 황금엑스산|분량 : 0.56|단위 : 그램|규격 : 생규|성분정보 : 황금으로서 1.25g;총량 : 1회 용량(5.00그램) 중|성분명 : 강활엑스산|분량 : 0.36|단위 : 그램|규격 : 생규|성분정보 : 강활으로서 1.25g;총량 : 1회 용량(5.00그램) 중|성분명 : 석고|분량 : 1.25|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(5.00그램) 중|성분명 : 작약엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 작약으로서 1.25g;총량 : 1회 용량(5.00그램) 중|성분명 : 승마엑스산|분량 : 0.20|단위 : 그램|규격 : 생규|성분정보 : 승마로서 1.25g;총량 : 1회 용량(5.00그램) 중|성분명 : 백지엑스산|분량 : 0.44|단위 : 그램|규격 : 생규|성분정보 : 백지로서 1.25g;총량 : 1회 용량(5.00그램) 중|성분명 : 길경엑스산|분량 : 0.54|단위 : 그램|규격 : 생규|성분정보 : 길경으로서 1.25g', '함량_총량기준': '1회 용량(5.00그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005593', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005593', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202104832', 'ITEM_NAME': '경방갈금련엑스과립(갈근황련황금탕)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초;황금;황련;갈근', 'ENTP_NAME': '경방신약(주)', 'CHART': '황갈색의 과립제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806613066806,8806613066813', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040006]감초|[M040789]황금|[M040792]황련|[M040004]갈근', '함량_원료성분원문': '총량 : 1회5.0그램|성분명 : 갈근|분량 : 2.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회5.0그램|성분명 : 황련|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회5.0그램|성분명 : 황금|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회5.0그램|성분명 : 감초|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '15.0', '수집URL': 'https://drug.hospitalk.net/item/202104832', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202104832', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005733', 'ITEM_NAME': '경방감초엑스산', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초', 'ENTP_NAME': '경방신약(주)', 'CHART': '담갈색의 입상형 가루', 'CHANGE_DATE': '2019-03-04', 'BAR_CODE': '8806613001807,8806613001814,8806613001821,8806613001838,8806613001845,8806613001852', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040006]감초', '함량_원료성분원문': '총량 : 본품 270밀리그램 중|성분명 : 감초|분량 : 1.0|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '본품 270밀리그램 중', '수집URL': 'https://drug.hospitalk.net/item/200005733', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005733', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201705471', 'ITEM_NAME': '경방감초엑스정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초 연조엑스(2.1∼2.5→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '적갈색의 장방형 필름코팅정제', 'CHANGE_DATE': '2026-07-22', 'BAR_CODE': '8806613047706,8806613047713,8806613047720,8806613047737,8806613047744,8806613047751,8806613047768,8806613047775', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M272009]감초 연조엑스(2.1∼2.5→1)', '함량_원료성분원문': '총량 : 1정650밀리그램|성분명 : 감초 연조엑스(2.1∼2.5→1)|분량 : 880.0|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1650', '수집URL': 'https://drug.hospitalk.net/item/201705471', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201705471', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201708619', 'ITEM_NAME': '경방경옥고', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '꿀;인삼;복령;생지황즙', 'ENTP_NAME': '경방신약(주)', 'CHART': '알루미늄 스틱포에 충전된 흑갈색의 점도가 있는 연조엑스제 또는 병(도자기)에 충전된 흑갈색의 점도가 있는 연조엑스제', 'CHANGE_DATE': '2020-10-07', 'BAR_CODE': '8806613048604,8806613048611,8806613048628,8806613048635,8806613048642,8806613048659,8806613049106,8806613049113', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M200168]꿀|[M040213]인삼|[M040225]복령|[M082091]생지황즙', '함량_원료성분원문': '총량 : 100g 중|성분명 : 생지황즙|분량 : 39.9|단위 : 그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 100g 중|성분명 : 복령|분량 : 12.4|단위 : 그램|규격 : KP|성분정보 : ;총량 : 100g 중|성분명 : 인삼|분량 : 6.2|단위 : 그램|규격 : KP|성분정보 : ;총량 : 100g 중|성분명 : 꿀|분량 : 41.5|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '100g 중', '수집URL': 'https://drug.hospitalk.net/item/201708619', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201708619', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005803', 'ITEM_NAME': '경방계지가용골모려탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '이상수침건조엑스;모려;용골;감초;생강;대추;작약;계지', 'ENTP_NAME': '경방신약(주)', 'CHART': '담갈색의 과립제', 'CHANGE_DATE': '2010-04-08', 'BAR_CODE': '8806613002507,8806613002514', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M099148]이상수침건조엑스|[M040180]모려|[M051196]용골|[M040006]감초|[M050752]생강|[M040071]대추|[M040523]작약|[M050037]계지', '함량_원료성분원문': '총량 : 1포 중 2.5그램|성분명 : 계지|분량 : 1.33|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포 중 2.5그램|성분명 : 작약|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : 패오니플로린으로서 26.6밀리그램;총량 : 1포 중 2.5그램|성분명 : 대추|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중 2.5그램|성분명 : 생강|분량 : 1.33|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포 중 2.5그램|성분명 : 감초|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : 글리시리진산으로서 13.4밀리그램;총량 : 1포 중 2.5그램|성분명 : 용골|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중 2.5그램|성분명 : 모려|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중 2.5그램|성분명 : 이상수침건조엑스|분량 : 850|단위 : 밀리그램|규격 : .|성분정보 :', '함량_총량기준': '1포 중 2.5그램', '수집URL': 'https://drug.hospitalk.net/item/200005803', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005803', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005652', 'ITEM_NAME': '경방공진단', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '인삼;사향;산수유;당귀;녹용', 'ENTP_NAME': '경방신약(주)', 'CHART': '금박을 환의한 흑갈색의 환제', 'CHANGE_DATE': '2021-08-03', 'BAR_CODE': '8806613003108,8806613003115,8806613003122,8806613003139,8806613003146', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040213]인삼|[M040253]사향|[M040257]산수유|[M040070]당귀|[M050139]녹용', '함량_원료성분원문': '총량 : 1환 (3.75g)중|성분명 : 녹용|분량 : 444.4|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환 (3.75g)중|성분명 : 당귀|분량 : 444.4|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환 (3.75g)중|성분명 : 산수유|분량 : 444.4|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환 (3.75g)중|성분명 : 사향|분량 : 74.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환 (3.75g)중|성분명 : 인삼|분량 : 444.4|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1환 (3.75g)중', '수집URL': 'https://drug.hospitalk.net/item/200005652', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005652', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201706375', 'ITEM_NAME': '경방구미강활탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초 연조엑스(2.1∼2.5→1);세신연조엑스(3.5~4.3→1);생지황 연조엑스(3.6~4.9→1);황금연조엑스(1.5~1.9→1);창출연조엑스(2.9~3.6→1);백지연조엑스(3.6~4.4→1);천궁 연조엑스(2.1∼2.6→1);방풍연조엑스(2.5~3.1→1);강활연조엑스(2.6~3.2→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2020-08-21', 'BAR_CODE': '8806613047904,8806613047911,8806613047928', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M272009]감초 연조엑스(2.1∼2.5→1)|[M279182]세신연조엑스(3.5~4.3→1)|[M273020]생지황 연조엑스(3.6~4.9→1)|[M266601]황금연조엑스(1.5~1.9→1)|[M266600]창출연조엑스(2.9~3.6→1)|[M266599]백지연조엑스(3.6~4.4→1)|[M274988]천궁 연조엑스(2.1∼2.6→1)|[M266597]방풍연조엑스(2.5~3.1→1)|[M266596]강활연조엑스(2.6~3.2→1)', '함량_원료성분원문': '총량 : 1회 용량(10g/포) 중|성분명 : 강활연조엑스(2.6~3.2→1)|분량 : 658.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 방풍연조엑스(2.5~3.1→1)|분량 : 676.8|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 천궁 연조엑스(2.1∼2.6→1)|분량 : 645.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 백지연조엑스(3.6~4.4→1)|분량 : 375.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 창출연조엑스(2.9~3.6→1)|분량 : 465.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 황금연조엑스(1.5~1.9→1)|분량 : 885.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 생지황 연조엑스(3.6~4.9→1)|분량 : 360.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 세신연조엑스(3.5~4.3→1)|분량 : 163.8|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 감초 연조엑스(2.1∼2.5→1)|분량 : 277.2|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회 용량(10g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/201706375', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201706375', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201607120', 'ITEM_NAME': '경방구미강활탕정(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초 연조엑스(2.1∼2.5→1);세신연조엑스(3.5~4.3→1);생지황 연조엑스(3.6~4.9→1);황금연조엑스(1.5~1.9→1);창출 연조엑스(2.9~3.6→1);백지 연조엑스(3.6~4.4→1);천궁 연조엑스(2.1∼2.6→1);방풍 연조엑스(2.5~3.1→1);강활 연조엑스(2.6~3.2→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '적갈색의 장방형 필름코팅정제', 'CHANGE_DATE': '2026-10-26', 'BAR_CODE': '8806613047607,8806613047614,8806613047621', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M272009]감초 연조엑스(2.1∼2.5→1)|[M279182]세신연조엑스(3.5~4.3→1)|[M273020]생지황 연조엑스(3.6~4.9→1)|[M117845]황금연조엑스(1.5~1.9→1)|[M117844]창출 연조엑스(2.9~3.6→1)|[M117843]백지 연조엑스(3.6~4.4→1)|[M274988]천궁 연조엑스(2.1∼2.6→1)|[M117841]방풍 연조엑스(2.5~3.1→1)|[M117840]강활 연조엑스(2.6~3.2→1)', '함량_원료성분원문': '총량 : 1회 용량(800mg/정 × 4정)|성분명 : 강활 연조엑스(2.6~3.2→1)|분량 : 658.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(800mg/정 × 4정)|성분명 : 방풍 연조엑스(2.5~3.1→1)|분량 : 676.8|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(800mg/정 × 4정)|성분명 : 천궁 연조엑스(2.1∼2.6→1)|분량 : 645.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(800mg/정 × 4정)|성분명 : 백지 연조엑스(3.6~4.4→1)|분량 : 375.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(800mg/정 × 4정)|성분명 : 창출 연조엑스(2.9~3.6→1)|분량 : 465.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(800mg/정 × 4정)|성분명 : 황금연조엑스(1.5~1.9→1)|분량 : 885.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(800mg/정 × 4정)|성분명 : 생지황 연조엑스(3.6~4.9→1)|분량 : 360.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(800mg/정 × 4정)|성분명 : 세신연조엑스(3.5~4.3→1)|분량 : 163.8|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(800mg/정 × 4정)|성분명 : 감초 연조엑스(2.1∼2.5→1)|분량 : 277.2|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회 용량(800mg/정 × 4정)', '수집URL': 'https://drug.hospitalk.net/item/201607120', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201607120', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005596', 'ITEM_NAME': '경방궁하탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '생강엑스산;감초엑스산;백출엑스산;지각엑스산;청피엑스산;진피엑스산;복령엑스산;반하엑스산;천궁엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613003603,8806613003610,8806613003627,8806613003634,8806613003641,8806613003658,8806613003665,8806613040806,8806613040813,8806613040820,8806613040837,8806613040844,8806613040851', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089512]생강엑스산|[M082727]감초엑스산|[M089527]백출엑스산|[M089552]지각엑스산|[M089586]청피엑스산|[M089506]진피엑스산|[M089528]복령엑스산|[M089568]반하엑스산|[M089533]천궁엑스산', '함량_원료성분원문': '총량 : 1회 용량(1.60그램) 중|성분명 : 천궁엑스산|분량 : 0.43|단위 : 그램|규격 : 생규|성분정보 : 천궁으로서 1.25g;총량 : 1회 용량(1.60그램) 중|성분명 : 반하엑스산|분량 : 0.31|단위 : 그램|규격 : 생규|성분정보 : 반하로서 1.25g;총량 : 1회 용량(1.60그램) 중|성분명 : 복령엑스산|분량 : 0.02|단위 : 그램|규격 : 생규|성분정보 : 복령으로서 1.25g;총량 : 1회 용량(1.60그램) 중|성분명 : 진피엑스산|분량 : 0.20|단위 : 그램|규격 : 생규|성분정보 : 진피로서 0.63g;총량 : 1회 용량(1.60그램) 중|성분명 : 청피엑스산|분량 : 0.19|단위 : 그램|규격 : 생규|성분정보 : 청피로서 0.63g;총량 : 1회 용량(1.60그램) 중|성분명 : 지각엑스산|분량 : 0.20|단위 : 그램|규격 : 생규|성분정보 : 지각으로서 0.63g;총량 : 1회 용량(1.60그램) 중|성분명 : 백출엑스산|분량 : 0.12|단위 : 그램|규격 : 생규|성분정보 : 백출으로서 0.31g;총량 : 1회 용량(1.60그램) 중|성분명 : 감초엑스산|분량 : 0.08|단위 : 그램|규격 : 생규|성분정보 : 감초로서 0.31g;총량 : 1회 용량(1.60그램) 중|성분명 : 생강엑스산|분량 : 0.05|단위 : 그램|규격 : 생규|성분정보 : 생강으로서 0.83g', '함량_총량기준': '1회 용량(1.60그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005596', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005596', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201802809', 'ITEM_NAME': '경방궁하탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '생강 연조엑스(5.1~6.9→1);감초 연조엑스(2.1∼2.5→1);백출연조엑스(2.8~3.4→1);지각 연조엑스(1.5~1.8→1);청피연조엑스(1.2~1.5→1);진피연조엑스(2.3~2.8→1);복령연조엑스(5.8~7.8→1);반하연조엑스(0.7~0.8→1);천궁연조엑스(2.1~2.6→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2020-07-27', 'BAR_CODE': '8806613049205,8806613049212,8806613049229', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M273014]생강 연조엑스(5.1~6.9→1)|[M272009]감초 연조엑스(2.1∼2.5→1)|[M279233]백출연조엑스(2.8~3.4→1)|[M117331]지각 연조엑스(1.5~1.8→1)|[M267912]청피연조엑스(1.2~1.5→1)|[M266591]진피연조엑스(2.3~2.8→1)|[M279232]복령연조엑스(5.8~7.8→1)|[M279231]반하연조엑스(0.7~0.8→1)|[M279230]천궁연조엑스(2.1~2.6→1)', '함량_원료성분원문': '총량 : 1회 용량(10g /포)|성분명 : 천궁연조엑스(2.1~2.6→1)|분량 : 537.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g /포)|성분명 : 반하연조엑스(0.7~0.8→1)|분량 : 1737.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g /포)|성분명 : 복령연조엑스(5.8~7.8→1)|분량 : 187.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g /포)|성분명 : 진피연조엑스(2.3~2.8→1)|분량 : 252.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g /포)|성분명 : 청피연조엑스(1.2~1.5→1)|분량 : 478.8|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g /포)|성분명 : 지각 연조엑스(1.5~1.8→1)|분량 : 390.6|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g /포)|성분명 : 백출연조엑스(2.8~3.4→1)|분량 : 102.3|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g /포)|성분명 : 감초 연조엑스(2.1∼2.5→1)|분량 : 136.4|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g /포)|성분명 : 생강 연조엑스(5.1~6.9→1)|분량 : 141.1|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1회 용량(10g /포)', '수집URL': 'https://drug.hospitalk.net/item/201802809', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201802809', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201604992', 'ITEM_NAME': '경방궁하탕정(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '생강연조엑스(5.1～6.9→1);감초연조엑스(2.1∼2.5→1);백출연조엑스(2.8～3.4→1);지각연조엑스(1.5∼1.8→1);청피연조엑스(1.2～1.5→1);진피연조엑스(2.3～2.8→1);복령연조엑스(5.8∼7.8→1);반하연조엑스(0.7∼0.8→1);천궁연조엑스(2.1～2.6→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '적갈색의 장방형 필름코팅정제', 'CHANGE_DATE': '2026-10-16', 'BAR_CODE': '8806613047300,8806613047317,8806613047324,8806613047331,8806613047348', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M280426]생강연조엑스(5.1～6.9→1)|[M280425]감초연조엑스(2.1∼2.5→1)|[M280433]백출연조엑스(2.8～3.4→1)|[M280432]지각연조엑스(1.5∼1.8→1)|[M280431]청피연조엑스(1.2～1.5→1)|[M280423]진피연조엑스(2.3～2.8→1)|[M280430]복령연조엑스(5.8∼7.8→1)|[M280429]반하연조엑스(0.7∼0.8→1)|[M280428]천궁연조엑스(2.1～2.6→1)', '함량_원료성분원문': '총량 : 1회 용량(700mg/정 x 2정)|성분명 : 천궁연조엑스(2.1～2.6→1)|분량 : 537.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700mg/정 x 2정)|성분명 : 반하연조엑스(0.7∼0.8→1)|분량 : 1737.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700mg/정 x 2정)|성분명 : 복령연조엑스(5.8∼7.8→1)|분량 : 187.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700mg/정 x 2정)|성분명 : 진피연조엑스(2.3～2.8→1)|분량 : 252.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700mg/정 x 2정)|성분명 : 청피연조엑스(1.2～1.5→1)|분량 : 478.8|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700mg/정 x 2정)|성분명 : 지각연조엑스(1.5∼1.8→1)|분량 : 390.6|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700mg/정 x 2정)|성분명 : 백출연조엑스(2.8～3.4→1)|분량 : 102.3|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700mg/정 x 2정)|성분명 : 감초연조엑스(2.1∼2.5→1)|분량 : 136.4|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700mg/정 x 2정)|성분명 : 생강연조엑스(5.1～6.9→1)|분량 : 141.1|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회 용량(700mg/정 x 2정)', '수집URL': 'https://drug.hospitalk.net/item/201604992', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201604992', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005597', 'ITEM_NAME': '경방내소산산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '삼릉엑스산;향부자엑스산;사인엑스산;신곡엑스산;산사엑스산;지실엑스산;복령엑스산;반하엑스산;건강엑스산;아출엑스산;진피엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613004006,8806613004013,8806613004020,8806613004037,8806613004044,8806613004051,8806613004068,8806613040905,8806613040912,8806613040929,8806613040936,8806613040943,8806613040950', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089606]삼릉엑스산|[M089589]향부자엑스산|[M089576]사인엑스산|[M089584]신곡엑스산|[M089698]산사엑스산|[M089604]지실엑스산|[M089528]복령엑스산|[M089568]반하엑스산|[M089572]건강엑스산|[M089699]아출엑스산|[M089506]진피엑스산', '함량_원료성분원문': '총량 : 1회 용량(3.25그램) 중|성분명 : 진피엑스산|분량 : 0.40|단위 : 그램|규격 : 생규|성분정보 : 진피로서 1.25g;총량 : 1회 용량(3.25그램) 중|성분명 : 아출엑스산|분량 : 0.11|단위 : 그램|규격 : 생규|성분정보 : 아출로서 1.25g;총량 : 1회 용량(3.25그램) 중|성분명 : 건강엑스산|분량 : 0.27|단위 : 그램|규격 : 생규|성분정보 : 건강으로서 1.25g;총량 : 1회 용량(3.25그램) 중|성분명 : 반하엑스산|분량 : 0.31|단위 : 그램|규격 : 생규|성분정보 : 반하로서 1.25g;총량 : 1회 용량(3.25그램) 중|성분명 : 복령엑스산|분량 : 0.02|단위 : 그램|규격 : 생규|성분정보 : 복령으로서 1.25g;총량 : 1회 용량(3.25그램) 중|성분명 : 지실엑스산|분량 : 0.36|단위 : 그램|규격 : 생규|성분정보 : 지실로서 1.25g;총량 : 1회 용량(3.25그램) 중|성분명 : 산사엑스산|분량 : 0.44|단위 : 그램|규격 : 생규|성분정보 : 산사로서 1.25g;총량 : 1회 용량(3.25그램) 중|성분명 : 신곡엑스산|분량 : 0.63|단위 : 그램|규격 : 생규|성분정보 : 신곡으로서 1.25g;총량 : 1회 용량(3.25그램) 중|성분명 : 사인엑스산|분량 : 0.15|단위 : 그램|규격 : 생규|성분정보 : 사인으로서 1.25g;총량 : 1회 용량(3.25그램) 중|성분명 : 향부자엑스산|분량 : 0.40|단위 : 그램|규격 : 생규|성분정보 : 향부자로서 1.25g;총량 : 1회 용량(3.25그램) 중|성분명 : 삼릉엑스산|분량 : 0.16|단위 : 그램|규격 : 생규|성분정보 : 삼릉으로서 1.25g', '함량_총량기준': '1회 용량(3.25그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005597', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005597', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202103143', 'ITEM_NAME': '경방내소산연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '삼릉연조엑스(5.4～7.2→1);향부자연조엑스(2.8~3.5→1);사인연조엑스(3.1∼3.8→1);신곡연조엑스(1.4∼1.7→1);산사연조엑스(2.2∼2.7→1);지실연조엑스(3.6~4.4→1);복령연조엑스(5.8~7.8→1);반하연조엑스(0.7~0.8→1);건강연조엑스(2.9~3.6→1);아출연조엑스(4.1～5.6→1);진피연조엑스(2.3~2.8→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '알루미늄포에 충전된 갈색의 연조엑스', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806613066509,8806613066516,8806613066523', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M280741]삼릉연조엑스(5.4～7.2→1)|[M268319]향부자연조엑스(2.8~3.5→1)|[M268069]사인연조엑스(3.1∼3.8→1)|[M267645]신곡연조엑스(1.4∼1.7→1)|[M268056]산사연조엑스(2.2∼2.7→1)|[M266607]지실연조엑스(3.6~4.4→1)|[M268326]복령연조엑스(5.8~7.8→1)|[M268073]반하연조엑스(0.7~0.8→1)|[M266876]건강연조엑스(2.9~3.6→1)|[M280742]아출연조엑스(4.1～5.6→1)|[M266591]진피연조엑스(2.3~2.8→1)', '함량_원료성분원문': '총량 : 1회 용량(10 g/포) 중 |성분명 : 진피연조엑스(2.3~2.8→1)|분량 : 500.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 아출연조엑스(4.1～5.6→1)|분량 : 265.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 건강연조엑스(2.9~3.6→1)|분량 : 387.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 반하연조엑스(0.7~0.8→1)|분량 : 1737.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 복령연조엑스(5.8~7.8→1)|분량 : 187.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 지실연조엑스(3.6~4.4→1)|분량 : 312.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 산사연조엑스(2.2∼2.7→1)|분량 : 512.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 신곡연조엑스(1.4∼1.7→1)|분량 : 800.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 사인연조엑스(3.1∼3.8→1)|분량 : 362.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 향부자연조엑스(2.8~3.5→1)|분량 : 400.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 삼릉연조엑스(5.4～7.2→1)|분량 : 202.5|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회 용량(10 g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/202103143', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202103143', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005600', 'ITEM_NAME': '경방대시호탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '반하엑스산;지실엑스산;대황엑스산;작약엑스산;황금엑스산;시호엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613004808,8806613004815,8806613004822,8806613004839,8806613004846,8806613004853,8806613004860,8806613041209,8806613041216,8806613041223,8806613041230,8806613041247,8806613041254', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089568]반하엑스산|[M089604]지실엑스산|[M089501]대황엑스산|[M090093]작약엑스산|[M089535]황금엑스산|[M089498]시호엑스산', '함량_원료성분원문': '총량 : 1회 용량(4.82그램) 중|성분명 : 시호엑스산|분량 : 0.85|단위 : 그램|규격 : 생규|성분정보 : 시호로서 5.00g;총량 : 1회 용량(4.82그램) 중|성분명 : 황금엑스산|분량 : 1.41|단위 : 그램|규격 : 생규|성분정보 : 황금으로서 3.13g;총량 : 1회 용량(4.82그램) 중|성분명 : 작약엑스산|분량 : 0.85|단위 : 그램|규격 : 생규|성분정보 : 작약으로서 3.13g;총량 : 1회 용량(4.82그램) 중|성분명 : 대황엑스산|분량 : 0.85|단위 : 그램|규격 : 생규|성분정보 : 대황으로서 2.50g;총량 : 1회 용량(4.82그램) 중|성분명 : 지실엑스산|분량 : 0.55|단위 : 그램|규격 : 생규|성분정보 : 지실로서 1.88g;총량 : 1회 용량(4.82그램) 중|성분명 : 반하엑스산|분량 : 0.31|단위 : 그램|규격 : 생규|성분정보 : 반하로서 1.25g', '함량_총량기준': '1회 용량(4.82그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005600', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005600', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005860', 'ITEM_NAME': '경방대시호탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대황;지실;대추;작약;황금;생강;반하;시호', 'ENTP_NAME': '경방신약(주)', 'CHART': '담갈색의 과립제', 'CHANGE_DATE': '2020-04-20', 'BAR_CODE': '8806613004907,8806613004914,8806613004921', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040073]대황|[M040536]지실|[M040071]대추|[M040523]작약|[M040789]황금|[M050752]생강|[M040202]반하|[M040336]시호', '함량_원료성분원문': '총량 : 1회 용량(3.0g) 중|성분명 : 시호|분량 : 2.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0g) 중|성분명 : 반하|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0g) 중|성분명 : 생강|분량 : 1.67|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.0g) 중|성분명 : 황금|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : 바이칼린으로서 100.0밀리그램;총량 : 1회 용량(3.0g) 중|성분명 : 작약|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : 패오니플로린으로서 20.0밀리그램;총량 : 1회 용량(3.0g) 중|성분명 : 대추|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0g) 중|성분명 : 지실|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0g) 중|성분명 : 대황|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1회 용량(3.0g) 중', '수집URL': 'https://drug.hospitalk.net/item/200005860', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005860', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201803195', 'ITEM_NAME': '경방대시호탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '반하연조엑스(0.7~0.8→1);지실연조엑스(3.6~4.4→1);대황연조엑스(2.3∼2.8→1);작약연조엑스(2.8~3.4→1);황금연조엑스(1.5~1.9→1);시호연조엑스(3.6~4.4→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2022-05-20', 'BAR_CODE': '8806613049403,8806613049410,8806613049427,8806613049434', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268073]반하연조엑스(0.7~0.8→1)|[M266607]지실연조엑스(3.6~4.4→1)|[M268072]대황연조엑스(2.3∼2.8→1)|[M268068]작약연조엑스(2.8~3.4→1)|[M266601]황금연조엑스(1.5~1.9→1)|[M266614]시호연조엑스(3.6~4.4→1)', '함량_원료성분원문': '총량 : 1회 용량(10 g/포) 중 |성분명 : 시호연조엑스(3.6~4.4→1)|분량 : 1250.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 황금연조엑스(1.5~1.9→1)|분량 : 1846.7|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 작약연조엑스(2.8~3.4→1)|분량 : 1032.9|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 대황연조엑스(2.3∼2.8→1)|분량 : 975.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 지실연조엑스(3.6~4.4→1)|분량 : 470.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포) 중 |성분명 : 반하연조엑스(0.7~0.8→1)|분량 : 1737.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1회 용량(10 g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/201803195', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201803195', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005601', 'ITEM_NAME': '경방대청룡탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대추엑스산;생강엑스산;석고;감초엑스산;행인엑스산;계지엑스산;마황엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613005003,8806613005010,8806613005027,8806613005034,8806613005041,8806613005058,8806613005065,8806613041308,8806613041315,8806613041322,8806613041339,8806613041346,8806613041353', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089515]대추엑스산|[M089512]생강엑스산|[M040279]석고|[M082727]감초엑스산|[M089575]행인엑스산|[M089525]계지엑스산|[M089573]마황엑스산', '함량_원료성분원문': '총량 : 1회 용량(6.82그램) 중|성분명 : 마황엑스산|분량 : 0.60|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(6.82그램) 중|성분명 : 계지엑스산|분량 : 0.08|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(6.82그램) 중|성분명 : 행인엑스산|분량 : 0.43|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(6.82그램) 중|성분명 : 감초엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(6.82그램) 중|성분명 : 석고|분량 : 5.00|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(6.82그램) 중|성분명 : 생강엑스산|분량 : 0.03|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(6.82그램) 중|성분명 : 대추엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '1회 용량(6.82그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005601', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005601', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005848', 'ITEM_NAME': '경방마자인환', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '행인;후박;작약;대황;지실;마인', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 환제', 'CHANGE_DATE': '2019-10-29', 'BAR_CODE': '8806613006208,8806613006215,8806613006222,8806613006246', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040769]행인|[M040813]후박|[M040523]작약|[M040073]대황|[M040536]지실|[M088617]마인', '함량_원료성분원문': '총량 : 1회 용량(3.2그램) 중|성분명 : 마인|분량 : 840.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.2그램) 중|성분명 : 지실|분량 : 342.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.2그램) 중|성분명 : 대황|분량 : 684.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.2그램) 중|성분명 : 작약|분량 : 342.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.2그램) 중|성분명 : 후박|분량 : 342.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.2그램) 중|성분명 : 행인|분량 : 426.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1회 용량(3.2그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005848', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005848', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005605', 'ITEM_NAME': '경방반하백출천마탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '백출엑스산;신곡엑스산;창출엑스산;인삼엑스산;황기엑스산;천마엑스산;맥아엑스산;진피엑스산;반하엑스산;복령엑스산;택사엑스산;건강엑스산;황백엑스산;생강엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613007601,8806613007618,8806613007625,8806613007632,8806613007649,8806613007656,8806613007663,8806613041704,8806613041711,8806613041728,8806613041735,8806613041742,8806613041759', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089527]백출엑스산|[M089584]신곡엑스산|[M089505]창출엑스산|[M051650]인삼엑스산|[M089579]황기엑스산|[M089642]천마엑스산|[M089626]맥아엑스산|[M089506]진피엑스산|[M089568]반하엑스산|[M089528]복령엑스산|[M089587]택사엑스산|[M089572]건강엑스산|[M085093]황백엑스산|[M089512]생강엑스산', '함량_원료성분원문': '총량 : 1회 용량(3.65그램) 중|성분명 : 반하엑스산|분량 : 0.47|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.65그램) 중|성분명 : 복령엑스산|분량 : 0.01|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.65그램) 중|성분명 : 택사엑스산|분량 : 0.11|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.65그램) 중|성분명 : 건강엑스산|분량 : 0.09|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.65그램) 중|성분명 : 황백엑스산|분량 : 0.06|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.65그램) 중|성분명 : 생강엑스산|분량 : 0.05|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.65그램) 중|성분명 : 진피엑스산|분량 : 0.60|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.65그램) 중|성분명 : 맥아엑스산|분량 : 0.47|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.65그램) 중|성분명 : 백출엑스산|분량 : 0.46|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.65그램) 중|성분명 : 신곡엑스산|분량 : 0.63|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.65그램) 중|성분명 : 창출엑스산|분량 : 0.24|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.65그램) 중|성분명 : 인삼엑스산|분량 : 0.15|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.65그램) 중|성분명 : 황기엑스산|분량 : 0.14|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.65그램) 중|성분명 : 천마엑스산|분량 : 0.17|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '1회 용량(3.65그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005605', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005605', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005809', 'ITEM_NAME': '경방반하백출천마탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '황기;신곡;생강;천마;맥아;복령;진피;백출;택사;황백;건강;인삼;반하', 'ENTP_NAME': '경방신약(주)', 'CHART': '담갈색의 과립제', 'CHANGE_DATE': '2020-04-13', 'BAR_CODE': '8806613007700,8806613007717', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040790]황기|[M050891]신곡|[M050752]생강|[M051379]천마|[M050407]맥아|[M040225]복령|[M040538]진피|[M040214]백출|[M040638]택사|[M040793]황백|[M040007]건강|[M051291]인삼|[M040202]반하', '함량_원료성분원문': '총량 : 1회 용량(3.0 그램) 중|성분명 : 반하|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0 그램) 중|성분명 : 인삼|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0 그램) 중|성분명 : 건강|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0 그램) 중|성분명 : 황백|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0 그램) 중|성분명 : 택사|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0 그램) 중|성분명 : 백출|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0 그램) 중|성분명 : 진피|분량 : 1|단위 : 그램|규격 : KP|성분정보 : 헤스페리딘으로서 40.0밀리그램;총량 : 1회 용량(3.0 그램) 중|성분명 : 복령|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0 그램) 중|성분명 : 맥아|분량 : 0.67|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.0 그램) 중|성분명 : 천마|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0 그램) 중|성분명 : 생강|분량 : 0.67|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.0 그램) 중|성분명 : 신곡|분량 : 0.67|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.0 그램) 중|성분명 : 황기|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1회 용량(3.0 그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005809', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005809', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201907549', 'ITEM_NAME': '경방반하백출천마탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '천마연조엑스(3.6∼4.9→1);황기 연조엑스(3.2~4.0→1);인삼 연조엑스(3.2~4.0→1);창출 연조엑스(2.9~3.6→1);신곡연조엑스(1.4∼1.7→1);백출연조엑스(2.8~3.4→1);맥아연조엑스(2.7∼3.3→1);진피 연조엑스(2.3~2.8→1);생강연조엑스(5.1~6.9→1);황백연조엑스(1.9~2.3→1);건강 연조엑스(2.9~3.6→1);택사연조엑스(4.1∼5.6→1);복령연조엑스(5.8~7.8→1);반하연조엑스(0.7~0.8→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2022-05-12', 'BAR_CODE': '8806613052601,8806613052618,8806613052625,8806613052632', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M270485]천마연조엑스(3.6∼4.9→1)|[M118042]황기 연조엑스(3.2~4.0→1)|[M117829]인삼 연조엑스(3.2~4.0→1)|[M117844]창출 연조엑스(2.9~3.6→1)|[M267645]신곡연조엑스(1.4∼1.7→1)|[M268184]백출연조엑스(2.8~3.4→1)|[M268057]맥아연조엑스(2.7∼3.3→1)|[M117835]진피 연조엑스(2.3~2.8→1)|[M268065]생강연조엑스(5.1~6.9→1)|[M268981]황백연조엑스(1.9~2.3→1)|[M117941]건강 연조엑스(2.9~3.6→1)|[M268059]택사연조엑스(4.1∼5.6→1)|[M268326]복령연조엑스(5.8~7.8→1)|[M268073]반하연조엑스(0.7~0.8→1)', '함량_원료성분원문': '총량 : 1회 용량(10 g/포)|성분명 : 반하연조엑스(0.7~0.8→1)|분량 : 2613.2|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포)|성분명 : 복령연조엑스(5.8~7.8→1)|분량 : 94.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포)|성분명 : 택사연조엑스(4.1∼5.6→1)|분량 : 132.3|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포)|성분명 : 건강 연조엑스(2.9~3.6→1)|분량 : 117.8|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포)|성분명 : 황백연조엑스(1.9~2.3→1)|분량 : 122.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포)|성분명 : 생강연조엑스(5.1~6.9→1)|분량 : 141.1|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포)|성분명 : 진피 연조엑스(2.3~2.8→1)|분량 : 752.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포)|성분명 : 맥아연조엑스(2.7∼3.3→1)|분량 : 639.2|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포)|성분명 : 백출연조엑스(2.8~3.4→1)|분량 : 412.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포)|성분명 : 신곡연조엑스(1.4∼1.7→1)|분량 : 800.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포)|성분명 : 창출 연조엑스(2.9~3.6→1)|분량 : 195.3|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포)|성분명 : 인삼 연조엑스(3.2~4.0→1)|분량 : 176.4|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포)|성분명 : 황기 연조엑스(3.2~4.0→1)|분량 : 176.4|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10 g/포)|성분명 : 천마연조엑스(3.6∼4.9→1)|분량 : 151.2|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1회 용량(10 g/포)', '수집URL': 'https://drug.hospitalk.net/item/201907549', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201907549', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005606', 'ITEM_NAME': '경방반하사심탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대추엑스산;생강엑스산;황련엑스산;건강엑스산;감초엑스산;인삼엑스산;황금엑스산;반하엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613007809,8806613007816,8806613007823,8806613007830,8806613007847,8806613007854,8806613007861,8806613041803,8806613041810,8806613041827,8806613041834,8806613041841,8806613041858', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089515]대추엑스산|[M089512]생강엑스산|[M089522]황련엑스산|[M089572]건강엑스산|[M082727]감초엑스산|[M051650]인삼엑스산|[M089535]황금엑스산|[M089568]반하엑스산', '함량_원료성분원문': '총량 : 1회 용량(3.19그램) 중|성분명 : 반하엑스산|분량 : 0.63|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.19그램) 중|성분명 : 황금엑스산|분량 : 0.85|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.19그램) 중|성분명 : 인삼엑스산|분량 : 0.45|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.19그램) 중|성분명 : 감초엑스산|분량 : 0.51|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.19그램) 중|성분명 : 건강엑스산|분량 : 0.27|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.19그램) 중|성분명 : 황련엑스산|분량 : 0.11|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.19그램) 중|성분명 : 생강엑스산|분량 : 0.03|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.19그램) 중|성분명 : 대추엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '1회 용량(3.19그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005606', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005606', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202500681', 'ITEM_NAME': '경방반하사심탕시럽', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '황련;대추;감초;인삼;건강;황금;반하', 'ENTP_NAME': '경방신약(주)', 'CHART': '알루미늄 포에 충전된 갈색의 시럽', 'CHANGE_DATE': '2025-10-22', 'BAR_CODE': '8806613072609,8806613072616,8806613072623,8806613072630', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040792]황련|[M040071]대추|[M040006]감초|[M051291]인삼|[M040007]건강|[M040789]황금|[M040202]반하', '함량_원료성분원문': '총량 : 1포20그램|성분명 : 반하|분량 : 1.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 황금|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 건강|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 인삼|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 감초|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 대추|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 황련|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '120', '수집URL': 'https://drug.hospitalk.net/item/202500681', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202500681', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202501202', 'ITEM_NAME': '경방방풍통성산연조엑스', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '길경;당귀;대황;마황;망초;박하;방풍;백출;황금;활석;감초;생강;석고;연교;작약;천궁;치자;형개', 'ENTP_NAME': '경방신약(주)', 'CHART': '알루미늄 포에 충전된 갈색의 연조엑스', 'CHANGE_DATE': '2026-01-30', 'BAR_CODE': '8806613072906,8806613072913,8806613072920', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040048]길경|[M040070]당귀|[M040073]대황|[M040135]마황|[M088654]망초|[M040198]박하|[M040205]방풍|[M040214]백출|[M040789]황금|[M071732]활석|[M040006]감초|[M050752]생강|[M040279]석고|[M051105]연교|[M040523]작약|[M040550]천궁|[M040564]치자|[M051936]형개', '함량_원료성분원문': '총량 : 1포20그램|성분명 : 감초|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 생강|분량 : 0.40|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포20그램|성분명 : 석고|분량 : 1.00|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포20그램|성분명 : 연교|분량 : 0.40|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 작약|분량 : 0.40|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 천궁|분량 : 0.40|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 치자|분량 : 0.40|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 형개|분량 : 0.40|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 활석|분량 : 1.67|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포20그램|성분명 : 황금|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 길경|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 당귀|분량 : 0.40|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 대황|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 마황|분량 : 0.40|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 망초|분량 : 0.50|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포20그램|성분명 : 박하|분량 : 0.40|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 방풍|분량 : 0.40|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 백출|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '120', '수집URL': 'https://drug.hospitalk.net/item/202501202', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202501202', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202500630', 'ITEM_NAME': '경방배농산급탕시럽', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '지실;작약;대추;길경;건강;감초', 'ENTP_NAME': '경방신약(주)', 'CHART': '알루미늄 포에 충전된 갈색의 시럽제', 'CHANGE_DATE': '2026-01-06', 'BAR_CODE': '8806613072401,8806613072418,8806613072425', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040536]지실|[M040523]작약|[M040071]대추|[M040048]길경|[M040007]건강|[M040006]감초', '함량_원료성분원문': '총량 : 1포20그램|성분명 : 감초|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 건강|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 길경|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 대추|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 작약|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 지실|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '120', '수집URL': 'https://drug.hospitalk.net/item/202500630', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202500630', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005609', 'ITEM_NAME': '경방보중익기탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시호엑스산;승마엑스산;진피엑스산;당귀엑스산;감초엑스산;백출엑스산;인삼엑스산;황기엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613008806,8806613008813,8806613008820,8806613008837,8806613008844,8806613008851,8806613008868,8806613008875,8806613042107,8806613042114,8806613042121,8806613042138,8806613042145,8806613042152', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089498]시호엑스산|[M089520]승마엑스산|[M089506]진피엑스산|[M089119]당귀엑스산|[M082727]감초엑스산|[M089527]백출엑스산|[M051650]인삼엑스산|[M089579]황기엑스산', '함량_원료성분원문': '총량 : 1회 용량(2.06그램) 중|성분명 : 황기엑스산|분량 : 0.41|단위 : 그램|규격 : 생규|성분정보 : 황기로서 1.88g;총량 : 1회 용량(2.06그램) 중|성분명 : 인삼엑스산|분량 : 0.30|단위 : 그램|규격 : 생규|성분정보 : 인삼으로서 1.25g;총량 : 1회 용량(2.06그램) 중|성분명 : 백출엑스산|분량 : 0.46|단위 : 그램|규격 : 생규|성분정보 : 백출로서 1.25g;총량 : 1회 용량(2.06그램) 중|성분명 : 감초엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 감초로서 1.25g;총량 : 1회 용량(2.06그램) 중|성분명 : 당귀엑스산|분량 : 0.23|단위 : 그램|규격 : 생규|성분정보 : 당귀로서 0.63g;총량 : 1회 용량(2.06그램) 중|성분명 : 진피엑스산|분량 : 0.20|단위 : 그램|규격 : 생규|성분정보 : 진피로서 0.63g;총량 : 1회 용량(2.06그램) 중|성분명 : 승마엑스산|분량 : 0.06|단위 : 그램|규격 : 생규|성분정보 : 승마로서 0.38g;총량 : 1회 용량(2.06그램) 중|성분명 : 시호엑스산|분량 : 0.06|단위 : 그램|규격 : 생규|성분정보 : 시호로서 0.38g', '함량_총량기준': '1회 용량(2.06그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005609', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005609', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005811', 'ITEM_NAME': '경방보중익기탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '승마;건강;감초;시호;진피;당귀;황기;백출;대추;인삼', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 과립제', 'CHANGE_DATE': '2019-11-14', 'BAR_CODE': '8806613008905,8806613008912', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040329]승마|[M040007]건강|[M040006]감초|[M040336]시호|[M040538]진피|[M040070]당귀|[M040790]황기|[M040214]백출|[M040071]대추|[M040213]인삼', '함량_원료성분원문': '총량 : 1회 용량(3.0그램) 중|성분명 : 인삼|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0그램) 중|성분명 : 대추|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0그램) 중|성분명 : 백출|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0그램) 중|성분명 : 황기|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0그램) 중|성분명 : 당귀|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0그램) 중|성분명 : 진피|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : 헤스페리딘으로서 26.8밀리그램;총량 : 1회 용량(3.0그램) 중|성분명 : 시호|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0그램) 중|성분명 : 감초|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : 글리시리진산으로서 10.0밀리그램;총량 : 1회 용량(3.0그램) 중|성분명 : 건강|분량 : 0.17|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0그램) 중|성분명 : 승마|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1회 용량(3.0그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005811', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005811', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201708568', 'ITEM_NAME': '경방보중익기탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시호연조엑스(3.6~4.4→1);승마연조엑스(4.3~5.9→1);진피연조엑스(2.3~2.8→1);당귀연조엑스(2.8~3.4→1);감초연조엑스(2.1∼2.5→1);백출연조엑스(2.8~3.4→1);인삼연조엑스(3.2~4.0→1);황기연조엑스(3.2~4.0→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄 포', 'CHANGE_DATE': '2022-07-05', 'BAR_CODE': '8806613048505,8806613048512,8806613048529,8806613048536', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M266614]시호연조엑스(3.6~4.4→1)|[M267152]승마연조엑스(4.3~5.9→1)|[M266591]진피연조엑스(2.3~2.8→1)|[M268188]당귀연조엑스(2.8~3.4→1)|[M268064]감초연조엑스(2.1∼2.5→1)|[M268184]백출연조엑스(2.8~3.4→1)|[M266585]인삼연조엑스(3.2~4.0→1)|[M267153]황기연조엑스(3.2~4.0→1)', '함량_원료성분원문': '총량 : 1회 용량(10g/포) 중|성분명 : 황기연조엑스(3.2~4.0→1)|분량 : 526.4|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 인삼연조엑스(3.2~4.0→1)|분량 : 350.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 백출연조엑스(2.8~3.4→1)|분량 : 412.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 감초연조엑스(2.1∼2.5→1)|분량 : 550.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 당귀연조엑스(2.8~3.4→1)|분량 : 207.9|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 진피연조엑스(2.3~2.8→1)|분량 : 252.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 승마연조엑스(4.3~5.9→1)|분량 : 76.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 시호연조엑스(3.6~4.4→1)|분량 : 95.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1회 용량(10g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/201708568', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201708568', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005611', 'ITEM_NAME': '경방복령보심탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '당귀엑스산;천궁엑스산;복령엑스산;인삼엑스산;반하엑스산;전호엑스산;진피엑스산;숙지황엑스산;대추엑스산;작약엑스산;지각엑스산;길경엑스산;갈근엑스산;자소엽엑스산;감초엑스산;생강엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613009308,8806613009315,8806613009322,8806613009339,8806613009346,8806613009353,8806613009360,8806613042305,8806613042312,8806613042329,8806613042336,8806613042343,8806613042350', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089119]당귀엑스산|[M089533]천궁엑스산|[M089528]복령엑스산|[M051650]인삼엑스산|[M089568]반하엑스산|[M089549]전호엑스산|[M089506]진피엑스산|[M089536]숙지황엑스산|[M089515]대추엑스산|[M090093]작약엑스산|[M089552]지각엑스산|[M084832]길경엑스산|[M089599]갈근엑스산|[M089623]자소엽엑스산|[M082727]감초엑스산|[M089512]생강엑스산', '함량_원료성분원문': '총량 : 1회 용량(4.83그램) 중|성분명 : 작약엑스산|분량 : 0.67|단위 : 그램|규격 : 생규|성분정보 : 작약으로서 2.5g;총량 : 1회 용량(4.83그램) 중|성분명 : 지각엑스산|분량 : 0.19|단위 : 그램|규격 : 생규|성분정보 : 지각으로서 0.63g;총량 : 1회 용량(4.83그램) 중|성분명 : 길경엑스산|분량 : 0.27|단위 : 그램|규격 : 생규|성분정보 : 길경으로서 0.63g;총량 : 1회 용량(4.83그램) 중|성분명 : 갈근엑스산|분량 : 0.29|단위 : 그램|규격 : 생규|성분정보 : 갈근으로서 0.63g;총량 : 1회 용량(4.83그램) 중|성분명 : 자소엽엑스산|분량 : 0.10|단위 : 그램|규격 : 생규|성분정보 : 자소엽으로서 0.63g;총량 : 1회 용량(4.83그램) 중|성분명 : 감초엑스산|분량 : 0.17|단위 : 그램|규격 : 생규|성분정보 : 감초로서 0.63g;총량 : 1회 용량(4.83그램) 중|성분명 : 생강엑스산|분량 : 0.05|단위 : 그램|규격 : 생규|성분정보 : 생강으로서 0.83g;총량 : 1회 용량(4.83그램) 중|성분명 : 대추엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 대추로서 0.67g;총량 : 1회 용량(4.83그램) 중|성분명 : 숙지황엑스산|분량 : 0.94|단위 : 그램|규격 : 생규|성분정보 : 숙지황으로서 1.88g;총량 : 1회 용량(4.83그램) 중|성분명 : 당귀엑스산|분량 : 0.60|단위 : 그램|규격 : 생규|성분정보 : 당귀로서 1.63g;총량 : 1회 용량(4.83그램) 중|성분명 : 천궁엑스산|분량 : 0.30|단위 : 그램|규격 : 생규|성분정보 : 천궁으로서 0.88g;총량 : 1회 용량(4.83그램) 중|성분명 : 복령엑스산|분량 : 0.02|단위 : 그램|규격 : 생규|성분정보 : 복령으로서 0.88g;총량 : 1회 용량(4.83그램) 중|성분명 : 인삼엑스산|분량 : 0.21|단위 : 그램|규격 : 생규|성분정보 : 인삼으로서 0.88g;총량 : 1회 용량(4.83그램) 중|성분명 : 반하엑스산|분량 : 0.22|단위 : 그램|규격 : 생규|성분정보 : 반하로서 0.88g;총량 : 1회 용량(4.83그램) 중|성분명 : 전호엑스산|분량 : 0.26|단위 : 그램|규격 : 생규|성분정보 : 전호으로서 0.88g;총량 : 1회 용량(4.83그램) 중|성분명 : 진피엑스산|분량 : 0.20|단위 : 그램|규격 : 생규|성분정보 : 진피로서 0.63g', '함량_총량기준': '1회 용량(4.83그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005611', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005611', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201906305', 'ITEM_NAME': '경방불환금정기산연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대추연조엑스(1.8~2.2→1);생강연조엑스(5.1~6.9→1);감초연조엑스(2.1∼2.5→1);반하연조엑스(0.7~0.8→1);곽향연조엑스(2.8~3.4→1);진피연조엑스(2.3~2.8→1);후박연조엑스(5.4∼7.4→1);창출연조엑스(2.9~3.6→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806613052205,8806613052212,8806613052229,8806613052236', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M266595]대추연조엑스(1.8~2.2→1)|[M268065]생강연조엑스(5.1~6.9→1)|[M268064]감초연조엑스(2.1∼2.5→1)|[M268061] 반하연조엑스(0.7~0.8→1)|[M268320]곽향연조엑스(2.8~3.4→1)|[M266591]진피연조엑스(2.3~2.8→1)|[M268058]후박연조엑스(5.4∼7.4→1)|[M266600]창출연조엑스(2.9~3.6→1)', '함량_원료성분원문': '총량 : 1회 용량 (10 g/포) 중|성분명 : 창출연조엑스(2.9~3.6→1)|분량 : 775.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량 (10 g/포) 중|성분명 : 후박연조엑스(5.4∼7.4→1)|분량 : 200.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량 (10 g/포) 중|성분명 : 진피연조엑스(2.3~2.8→1)|분량 : 500.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량 (10 g/포) 중|성분명 : 곽향연조엑스(2.8~3.4→1)|분량 : 412.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량 (10 g/포) 중|성분명 :  반하연조엑스(0.7~0.8→1)|분량 : 1737.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량 (10 g/포) 중|성분명 : 감초연조엑스(2.1∼2.5→1)|분량 : 550.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량 (10 g/포) 중|성분명 : 생강연조엑스(5.1~6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량 (10 g/포) 중|성분명 : 대추연조엑스(1.8~2.2→1)|분량 : 341.7|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1회 용량 (10 g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/201906305', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201906305', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202006738', 'ITEM_NAME': '경방산조인탕정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초초연조엑스(2.9∼3.6→1);건강 연조엑스(2.9~3.6→1);천궁 연조엑스(2.1∼2.6→1);복령 연조엑스(5.8∼7.8→1);지모 연조엑스(2.4∼2.9→1);맥문동 연조엑스(2.4∼2.9→1);산조인초연조엑스(7.6∼11.4→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '적갈색의 장방형 필름코팅정제', 'CHANGE_DATE': '2026-01-28', 'BAR_CODE': '8806613065304,8806613065311,8806613065328,8806613065335,8806613065342', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M279621]감초초연조엑스(2.9∼3.6→1)|[M117941]건강 연조엑스(2.9~3.6→1)|[M274988]천궁 연조엑스(2.1∼2.6→1)|[M272852]복령 연조엑스(5.8∼7.8→1)|[M274955]지모 연조엑스(2.4∼2.9→1)|[M272556]맥문동 연조엑스(2.4∼2.9→1)|[M279573]산조인초연조엑스(7.6∼11.4→1)', '함량_원료성분원문': '총량 : 1 정 800 mg 중|성분명 : 산조인초연조엑스(7.6∼11.4→1)|분량 : 137.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1 정 800 mg 중|성분명 : 맥문동 연조엑스(2.4∼2.9→1)|분량 : 356.3|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1 정 800 mg 중|성분명 : 지모 연조엑스(2.4∼2.9→1)|분량 : 356.3|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1 정 800 mg 중|성분명 : 복령 연조엑스(5.8∼7.8→1)|분량 : 93.8|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1 정 800 mg 중|성분명 : 천궁 연조엑스(2.1∼2.6→1)|분량 : 268.8|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1 정 800 mg 중|성분명 : 건강 연조엑스(2.9~3.6→1)|분량 : 48.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1 정 800 mg 중|성분명 : 감초초연조엑스(2.9∼3.6→1)|분량 : 48.5|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1 정 800 mg 중', '수집URL': 'https://drug.hospitalk.net/item/202006738', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202006738', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005613', 'ITEM_NAME': '경방삼소음산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '갈근엑스산;복령엑스산;진피엑스산;길경엑스산;지각엑스산;반하엑스산;전호엑스산;자소엽엑스산;대추엑스산;생강엑스산;감초엑스산;인삼엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613010007,8806613010014,8806613010021,8806613010038,8806613010045,8806613010052,8806613010069,8806613010076,8806613042503,8806613042510,8806613042527,8806613042534,8806613042541,8806613042558', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089599]갈근엑스산|[M089528]복령엑스산|[M089506]진피엑스산|[M084832]길경엑스산|[M089552]지각엑스산|[M089568]반하엑스산|[M089549]전호엑스산|[M089623]자소엽엑스산|[M089515]대추엑스산|[M089512]생강엑스산|[M082727]감초엑스산|[M051650]인삼엑스산', '함량_원료성분원문': '총량 : 1회 용량(3.36그램) 중|성분명 : 인삼엑스산|분량 : 0.30|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.36그램) 중|성분명 : 감초엑스산|분량 : 0.25|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.36그램) 중|성분명 : 생강엑스산|분량 : 0.03|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.36그램) 중|성분명 : 대추엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.36그램) 중|성분명 : 자소엽엑스산|분량 : 0.20|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.36그램) 중|성분명 : 전호엑스산|분량 : 0.36|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.36그램) 중|성분명 : 반하엑스산|분량 : 0.31|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.36그램) 중|성분명 : 갈근엑스산|분량 : 0.56|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.36그램) 중|성분명 : 복령엑스산|분량 : 0.02|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.36그램) 중|성분명 : 진피엑스산|분량 : 0.30|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.36그램) 중|성분명 : 길경엑스산|분량 : 0.40|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3.36그램) 중|성분명 : 지각엑스산|분량 : 0.29|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '1회 용량(3.36그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005613', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005613', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201803839', 'ITEM_NAME': '경방삼소음연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '갈근연조엑스(2.5~3.1→1);복령연조엑스(5.8~7.8→1);진피연조엑스(2.3~2.8→1);길경연조엑스(2.3∼2.8→1);지각연조엑스(1.5~1.8→1);반하연조엑스(0.7~0.8→1);전호연조엑스(2.0~2.4→1);인삼연조엑스(3.2~4.0→1);감초연조엑스(2.1∼2.5→1);생강연조엑스(5.1~6.9→1);대추연조엑스(1.8~2.2→1);자소엽연조엑스(2.7~3.3→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2020-07-21', 'BAR_CODE': '8806613050003,8806613050010,8806613050027,8806613050034', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M266589]갈근연조엑스(2.5~3.1→1)|[M268326]복령연조엑스(5.8~7.8→1)|[M266591]진피연조엑스(2.3~2.8→1)|[M261226]길경연조엑스(2.3∼2.8→1) |[M264376]지각연조엑스(1.5~1.8→1)|[M268073]반하연조엑스(0.7~0.8→1)|[M266587]전호연조엑스(2.0~2.4→1)|[M266585]인삼연조엑스(3.2~4.0→1)|[M268064]감초연조엑스(2.1∼2.5→1)|[M268065]생강연조엑스(5.1~6.9→1)|[M266595]대추연조엑스(1.8~2.2→1)|[M268325]자소엽연조엑스(2.7~3.3→1)', '함량_원료성분원문': '총량 : 1회 용량(10g/포) 중|성분명 : 인삼연조엑스(3.2~4.0→1)|분량 : 350.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 감초연조엑스(2.1∼2.5→1)|분량 : 413.6|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 생강연조엑스(5.1~6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 대추연조엑스(1.8~2.2→1)|분량 : 341.7|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 자소엽연조엑스(2.7~3.3→1)|분량 : 425.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 전호연조엑스(2.0~2.4→1)|분량 : 575.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 반하연조엑스(0.7~0.8→1)|분량 : 1,737.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 갈근연조엑스(2.5~3.1→1)|분량 : 450.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 복령연조엑스(5.8~7.8→1)|분량 : 187.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 진피연조엑스(2.3~2.8→1)|분량 : 376.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 길경연조엑스(2.3∼2.8→1) |분량 : 366.6|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 지각연조엑스(1.5~1.8→1)|분량 : 582.8|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1회 용량(10g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/201803839', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201803839', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201706370', 'ITEM_NAME': '경방삼소음정(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '갈근연조엑스(2.5~3.1→1);복령 연조엑스(5.8∼7.8→1);진피연조엑스(2.3~2.8→1);길경 연조엑스(2.3∼2.8→1);지각 연조엑스(1.5~1.8→1);반하 연조엑스(0.7∼0.8→1);전호연조엑스(2.0~2.4→1);자소엽 연조엑스(2.7∼3.3→1);대추연조엑스(1.8~2.2→1);생강 연조엑스(5.1~6.9→1);감초 연조엑스(2.1∼2.5→1);인삼연조엑스(3.2~4.0→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 장방형 코팅정제', 'CHANGE_DATE': '2022-01-10', 'BAR_CODE': '8806613048000,8806613048017,8806613048024', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M266589]갈근연조엑스(2.5~3.1→1)|[M272852]복령 연조엑스(5.8∼7.8→1)|[M266591]진피연조엑스(2.3~2.8→1)|[M272159]길경 연조엑스(2.3∼2.8→1)|[M117331]지각 연조엑스(1.5~1.8→1)|[M272755]반하 연조엑스(0.7∼0.8→1)|[M266587]전호연조엑스(2.0~2.4→1)|[M273975]자소엽 연조엑스(2.7∼3.3→1)|[M266595]대추연조엑스(1.8~2.2→1)|[M273014]생강 연조엑스(5.1~6.9→1)|[M272009]감초 연조엑스(2.1∼2.5→1)|[M266585]인삼연조엑스(3.2~4.0→1)', '함량_원료성분원문': '총량 : 1회 용량(700 mg/정 x 4정) 중 |성분명 : 인삼연조엑스(3.2~4.0→1)|분량 : 350.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700 mg/정 x 4정) 중 |성분명 : 감초 연조엑스(2.1∼2.5→1)|분량 : 413.6|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700 mg/정 x 4정) 중 |성분명 : 생강 연조엑스(5.1~6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700 mg/정 x 4정) 중 |성분명 : 대추연조엑스(1.8~2.2→1)|분량 : 341.7|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700 mg/정 x 4정) 중 |성분명 : 자소엽 연조엑스(2.7∼3.3→1)|분량 : 425.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700 mg/정 x 4정) 중 |성분명 : 전호연조엑스(2.0~2.4→1)|분량 : 575.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700 mg/정 x 4정) 중 |성분명 : 반하 연조엑스(0.7∼0.8→1)|분량 : 1737.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700 mg/정 x 4정) 중 |성분명 : 갈근연조엑스(2.5~3.1→1)|분량 : 450.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700 mg/정 x 4정) 중 |성분명 : 복령 연조엑스(5.8∼7.8→1)|분량 : 187.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700 mg/정 x 4정) 중 |성분명 : 진피연조엑스(2.3~2.8→1)|분량 : 376.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700 mg/정 x 4정) 중 |성분명 : 길경 연조엑스(2.3∼2.8→1)|분량 : 366.6|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(700 mg/정 x 4정) 중 |성분명 : 지각 연조엑스(1.5~1.8→1)|분량 : 582.8|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회 용량(700 mg/정 x 4정) 중', '수집URL': 'https://drug.hospitalk.net/item/201706370', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201706370', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201706371', 'ITEM_NAME': '경방삼출건비탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '후박연조엑스(5.4~7.4→1);진피연조엑스(2.3~2.8→1);산사연조엑스(2.2~2.7→1);지실연조엑스(3.6~4.4→1);작약 연조엑스(2.8~3.4→1);사인연조엑스(3.1~3.8→1);복령연조엑스(5.8~7.8→1);백출연조엑스(2.8~3.4→1);대추연조엑스(1.8~2.2→1);생강 연조엑스(5.1~6.9→1);감초 연조엑스(2.1∼2.5→1);맥아연조엑스(2.7~3.3→1);신곡연조엑스(1.4~1.7→1);인삼연조엑스(3.2~4.0→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2020-10-30', 'BAR_CODE': '8806613048208,8806613048215,8806613048222,8806613048239', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M279834]후박연조엑스(5.4~7.4→1)|[M266591]진피연조엑스(2.3~2.8→1)|[M279835]산사연조엑스(2.2~2.7→1)|[M266607]지실연조엑스(3.6~4.4→1)|[M117955]작약 연조엑스(2.8~3.4→1)|[M279836]사인연조엑스(3.1~3.8→1)|[M279833]복령연조엑스(5.8~7.8→1)|[M279832]백출연조엑스(2.8~3.4→1)|[M266595]대추연조엑스(1.8~2.2→1)|[M273014]생강 연조엑스(5.1~6.9→1)|[M272009]감초 연조엑스(2.1∼2.5→1)|[M279838]맥아연조엑스(2.7~3.3→1)|[M279837]신곡연조엑스(1.4~1.7→1)|[M266585]인삼연조엑스(3.2~4.0→1)', '함량_원료성분원문': '총량 : 1회 용량(10g/포) 중|성분명 : 인삼연조엑스(3.2~4.0→1)|분량 : 350.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 신곡연조엑스(1.4~1.7→1)|분량 : 403.2|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 맥아연조엑스(2.7~3.3→1)|분량 : 214.2|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 감초 연조엑스(2.1∼2.5→1)|분량 : 277.2|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 생강 연조엑스(5.1~6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 대추연조엑스(1.8~2.2→1)|분량 : 341.7|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 백출연조엑스(2.8~3.4→1)|분량 : 412.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 복령연조엑스(5.8~7.8→1)|분량 : 187.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 후박연조엑스(5.4~7.4→1)|분량 : 200.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 진피연조엑스(2.3~2.8→1)|분량 : 500.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 산사연조엑스(2.2~2.7→1)|분량 : 512.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 지실연조엑스(3.6~4.4→1)|분량 : 250.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 작약 연조엑스(2.8~3.4→1)|분량 : 330.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 사인연조엑스(3.1~3.8→1)|분량 : 182.7|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회 용량(10g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/201706371', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201706371', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005865', 'ITEM_NAME': '경방생강사심탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '생강;건강;황련;대추;감초;황금;인삼;반하', 'ENTP_NAME': '경방신약(주)', 'CHART': '담갈색의 과립제', 'CHANGE_DATE': '2020-04-20', 'BAR_CODE': '8806613010601,8806613010618', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050752]생강|[M040007]건강|[M040792]황련|[M040071]대추|[M040006]감초|[M040789]황금|[M051291]인삼|[M040202]반하', '함량_원료성분원문': '총량 : 1회2.5그램|성분명 : 반하|분량 : 2.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회2.5그램|성분명 : 인삼|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회2.5그램|성분명 : 황금|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : 바이칼린으로서 100.0밀리그램;총량 : 1회2.5그램|성분명 : 감초|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : 글리시리진산으로서 20.0밀리그램;총량 : 1회2.5그램|성분명 : 대추|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회2.5그램|성분명 : 황련|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : 베르베린으로서 11.6밀리그램;총량 : 1회2.5그램|성분명 : 건강|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회2.5그램|성분명 : 생강|분량 : 1.33|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '12.5', '수집URL': 'https://drug.hospitalk.net/item/200005865', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005865', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202200987', 'ITEM_NAME': '경방생맥산연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '맥문동 연조엑스(2.4∼2.9→1);인삼 연조엑스(3.2~4.0→1);오미자 연조엑스(3.6~4.4→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2022-05-23', 'BAR_CODE': '8806613067605,8806613067612,8806613067629', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M272556]맥문동 연조엑스(2.4∼2.9→1)|[M117829]인삼 연조엑스(3.2~4.0→1)|[M117939]오미자 연조엑스(3.6~4.4→1)', '함량_원료성분원문': '총량 : 1회 용량(10g/포) 중|성분명 : 맥문동 연조엑스(2.4∼2.9→1)|분량 : 950.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 인삼 연조엑스(3.2~4.0→1)|분량 : 350.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 오미자 연조엑스(3.6~4.4→1)|분량 : 312.5|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회 용량(10g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/202200987', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202200987', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005618', 'ITEM_NAME': '경방소시호탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대추엑스산;생강엑스산;감초엑스산;반하엑스산;인삼엑스산;황금엑스산;시호엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613011301,8806613011318,8806613011325,8806613011332,8806613011349,8806613011356,8806613011363,8806613043005,8806613043012,8806613043029,8806613043036,8806613043043,8806613043050', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089515]대추엑스산|[M089512]생강엑스산|[M082727]감초엑스산|[M089568]반하엑스산|[M051650]인삼엑스산|[M089535]황금엑스산|[M089498]시호엑스산', '함량_원료성분원문': '총량 : 1회 용량(2.92그램) 중|성분명 : 시호엑스산|분량 : 0.64|단위 : 그램|규격 : 생규|성분정보 : 시호로서 3.75g;총량 : 1회 용량(2.92그램) 중|성분명 : 황금엑스산|분량 : 1.13|단위 : 그램|규격 : 생규|성분정보 : 황금으로서 2.5g;총량 : 1회 용량(2.92그램) 중|성분명 : 인삼엑스산|분량 : 0.30|단위 : 그램|규격 : 생규|성분정보 : 인삼으로서 1.25g;총량 : 1회 용량(2.92그램) 중|성분명 : 반하엑스산|분량 : 0.31|단위 : 그램|규격 : 생규|성분정보 : 반하로서 1.25g;총량 : 1회 용량(2.92그램) 중|성분명 : 감초엑스산|분량 : 0.17|단위 : 그램|규격 : 생규|성분정보 : 감초로서 0.63g;총량 : 1회 용량(2.92그램) 중|성분명 : 생강엑스산|분량 : 0.03|단위 : 그램|규격 : 생규|성분정보 : 생강으로서 0.50g;총량 : 1회 용량(2.92그램) 중|성분명 : 대추엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 대추로서 0.67g', '함량_총량기준': '1회 용량(2.92그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005618', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005618', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201906132', 'ITEM_NAME': '경방소시호탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대추 연조엑스(1.8~2.2→1);생강연조엑스(5.1~6.9→1);감초연조엑스(2.1~2.5→1);반하연조엑스(0.7~0.8→1);인삼 연조엑스(3.2~4.0→1);황금연조엑스(1.5~1.9→1);시호 연조엑스(3.6~4.4→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806613052106,8806613052113,8806613052120,8806613052137', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M117839]대추 연조엑스(1.8~2.2→1)|[M268065]생강연조엑스(5.1~6.9→1)|[M268186]감초연조엑스(2.1~2.5→1)|[M268073]반하연조엑스(0.7~0.8→1)|[M117829]인삼 연조엑스(3.2~4.0→1)|[M117845]황금연조엑스(1.5~1.9→1)|[M117858]시호 연조엑스(3.6~4.4→1)', '함량_원료성분원문': '총량 : 1회 용량(10g/포) 중|성분명 : 시호 연조엑스(3.6~4.4→1)|분량 : 937.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 황금연조엑스(1.5~1.9→1)|분량 : 1475.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 인삼 연조엑스(3.2~4.0→1)|분량 : 350.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 반하연조엑스(0.7~0.8→1)|분량 : 1737.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 감초연조엑스(2.1~2.5→1)|분량 : 277.2|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 생강연조엑스(5.1~6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 대추 연조엑스(1.8~2.2→1)|분량 : 341.7|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1회 용량(10g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/201906132', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201906132', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005619', 'ITEM_NAME': '경방소청룡탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건강엑스산;감초엑스산;세신엑스산;계지엑스산;오미자엑스산;반하엑스산;작약엑스산;마황엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613011509,8806613011516,8806613011523,8806613011530,8806613011547,8806613011554,8806613011561,8806613011578,8806613043104,8806613043111,8806613043128,8806613043135,8806613043142,8806613043159', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089572]건강엑스산|[M082727]감초엑스산|[M089608]세신엑스산|[M089525]계지엑스산|[M089619]오미자엑스산|[M089568]반하엑스산|[M090093]작약엑스산|[M089573]마황엑스산', '함량_원료성분원문': '총량 : 1회 용량(2.67그램) 중|성분명 : 마황엑스산|분량 : 0.30|단위 : 그램|규격 : 생규|성분정보 : 마황으로서 1.88g;총량 : 1회 용량(2.67그램) 중|성분명 : 작약엑스산|분량 : 0.51|단위 : 그램|규격 : 생규|성분정보 : 작약으로서 1.88g;총량 : 1회 용량(2.67그램) 중|성분명 : 반하엑스산|분량 : 0.47|단위 : 그램|규격 : 생규|성분정보 : 반하로서 1.88g;총량 : 1회 용량(2.67그램) 중|성분명 : 오미자엑스산|분량 : 0.55|단위 : 그램|규격 : 생규|성분정보 : 오미자로서 1.88g;총량 : 1회 용량(2.67그램) 중|성분명 : 계지엑스산|분량 : 0.04|단위 : 그램|규격 : 생규|성분정보 : 계지로서 1.25g;총량 : 1회 용량(2.67그램) 중|성분명 : 세신엑스산|분량 : 0.18|단위 : 그램|규격 : 생규|성분정보 : 세신으로서 1.25g;총량 : 1회 용량(2.67그램) 중|성분명 : 감초엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 감초로서 1.25g;총량 : 1회 용량(2.67그램) 중|성분명 : 건강엑스산|분량 : 0.28|단위 : 그램|규격 : 생규|성분정보 : 건강으로서 1.25g', '함량_총량기준': '1회 용량(2.67그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005619', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005619', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201707336', 'ITEM_NAME': '경방소청룡탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건강연조엑스(2.9~3.6→1);감초연조엑스(2.1∼2.5→1);세신연조엑스(3.5~4.3→1);계지연조엑스(7.6~11.4→1);오미자연조엑스(3.6~4.4→1);반하연조엑스(0.7~0.8→1);작약연조엑스(2.8~3.4→1);마황연조엑스(3.8~5.1→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 든 알루미늄 포', 'CHANGE_DATE': '2020-07-21', 'BAR_CODE': '8806613048307,8806613048314,8806613048321', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M266876]건강연조엑스(2.9~3.6→1)|[M268064]감초연조엑스(2.1∼2.5→1)|[M279182]세신연조엑스(3.5~4.3→1)|[M279181]계지연조엑스(7.6~11.4→1)|[M266874]오미자연조엑스(3.6~4.4→1)|[M268061] 반하연조엑스(0.7~0.8→1)|[M268187]작약연조엑스(2.8~3.4→1)|[M279180]마황연조엑스(3.8~5.1→1)', '함량_원료성분원문': '총량 : 1회 용량(10g/포) 중|성분명 : 마황연조엑스(3.8~5.1→1)|분량 : 432.4|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 작약연조엑스(2.8~3.4→1)|분량 : 620.4|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 :  반하연조엑스(0.7~0.8→1)|분량 : 2613.2|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 오미자연조엑스(3.6~4.4→1)|분량 : 470.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 계지연조엑스(7.6~11.4→1)|분량 : 137.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 세신연조엑스(3.5~4.3→1)|분량 : 325.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 감초연조엑스(2.1∼2.5→1)|분량 : 550.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 건강연조엑스(2.9~3.6→1)|분량 : 387.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1회 용량(10g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/201707336', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201707336', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201604973', 'ITEM_NAME': '경방소청룡탕정(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건강연조엑스(2.9～3.6→1);감초연조엑스(2.1∼2.5→1);세신연조엑스(3.5～4.3→1);계지연조엑스(7.6～11.4→1);오미자연조엑스(3.6～4.4→1);반하연조엑스(0.7∼0.8→1);작약연조엑스(2.8～3.4→1);마황연조엑스(3.8∼5.1→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '적갈색의 장방형 필름코팅정제', 'CHANGE_DATE': '2026-10-26', 'BAR_CODE': '8806613047201,8806613047218,8806613047225', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M280395]건강연조엑스(2.9～3.6→1)|[M280394]감초연조엑스(2.1∼2.5→1)|[M280393]세신연조엑스(3.5～4.3→1)|[M280392]계지연조엑스(7.6～11.4→1)|[M280391]오미자연조엑스(3.6～4.4→1)|[M280390]반하연조엑스(0.7∼0.8→1)|[M280389]작약연조엑스(2.8～3.4→1)|[M280388]마황연조엑스(3.8∼5.1→1)', '함량_원료성분원문': '총량 :  1회 용량(800 mg/정 x 3 정) 중|성분명 : 마황연조엑스(3.8∼5.1→1)|분량 : 432.4|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 :  1회 용량(800 mg/정 x 3 정) 중|성분명 : 작약연조엑스(2.8～3.4→1)|분량 : 620.4|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 :  1회 용량(800 mg/정 x 3 정) 중|성분명 : 반하연조엑스(0.7∼0.8→1)|분량 : 2613.2|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 :  1회 용량(800 mg/정 x 3 정) 중|성분명 : 오미자연조엑스(3.6～4.4→1)|분량 : 470.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 :  1회 용량(800 mg/정 x 3 정) 중|성분명 : 계지연조엑스(7.6～11.4→1)|분량 : 137.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 :  1회 용량(800 mg/정 x 3 정) 중|성분명 : 세신연조엑스(3.5～4.3→1)|분량 : 325.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 :  1회 용량(800 mg/정 x 3 정) 중|성분명 : 감초연조엑스(2.1∼2.5→1)|분량 : 550.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 :  1회 용량(800 mg/정 x 3 정) 중|성분명 : 건강연조엑스(2.9～3.6→1)|분량 : 387.5|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회 용량(800 mg/정 x 3 정) 중', '수집URL': 'https://drug.hospitalk.net/item/201604973', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201604973', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005621', 'ITEM_NAME': '경방시경반하탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초엑스산;행인엑스산;청피엑스산;길경엑스산;지각엑스산;황금엑스산;반하엑스산;괄루인엑스산;생강엑스산;시호엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613012209,8806613012216,8806613012223,8806613012230,8806613012247,8806613012254,8806613012261,8806613043302,8806613043319,8806613043326,8806613043333,8806613043340,8806613043357', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M082727]감초엑스산|[M089575]행인엑스산|[M089586]청피엑스산|[M084832]길경엑스산|[M089552]지각엑스산|[M089535]황금엑스산|[M089568]반하엑스산|[M089609]괄루인엑스산|[M089512]생강엑스산|[M089498]시호엑스산', '함량_원료성분원문': '총량 : 1회 용량(3.00그램) 중|성분명 : 시호엑스산|분량 : 0.42|단위 : 그램|규격 : 생규|성분정보 : 시호로서 2.50 g;총량 : 1회 용량(3.00그램) 중|성분명 : 생강엑스산|분량 : 0.03|단위 : 그램|규격 : 생규|성분정보 : 생강으로서 0.50 g;총량 : 1회 용량(3.00그램) 중|성분명 : 괄루인엑스산|분량 : 0.07|단위 : 그램|규격 : 생규|성분정보 : 괄루인으로서 1.25 g;총량 : 1회 용량(3.00그램) 중|성분명 : 반하엑스산|분량 : 0.31|단위 : 그램|규격 : 생규|성분정보 : 반하로서 1.25 g;총량 : 1회 용량(3.00그램) 중|성분명 : 황금엑스산|분량 : 0.56|단위 : 그램|규격 : 생규|성분정보 : 황금으로서 1.25 g;총량 : 1회 용량(3.00그램) 중|성분명 : 지각엑스산|분량 : 0.39|단위 : 그램|규격 : 생규|성분정보 : 지각으로서 1.25 g;총량 : 1회 용량(3.00그램) 중|성분명 : 길경엑스산|분량 : 0.54|단위 : 그램|규격 : 생규|성분정보 : 길경으로서 1.25 g;총량 : 1회 용량(3.00그램) 중|성분명 : 청피엑스산|분량 : 0.31|단위 : 그램|규격 : 생규|성분정보 : 청피로서 1.00 g;총량 : 1회 용량(3.00그램) 중|성분명 : 행인엑스산|분량 : 0.23|단위 : 그램|규격 : 생규|성분정보 : 행인으로서 1.00 g;총량 : 1회 용량(3.00그램) 중|성분명 : 감초엑스산|분량 : 0.14|단위 : 그램|규격 : 생규|성분정보 : 감초로서 0.50 g', '함량_총량기준': '1회 용량(3.00그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005621', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005621', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005622', 'ITEM_NAME': '경방시호계지탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대추엑스산;생강엑스산;감초엑스산;반하엑스산;작약엑스산;인삼엑스산;황금엑스산;계지엑스산;시호엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613012308,8806613012315,8806613012322,8806613012339,8806613012346,8806613012353,8806613012360,8806613043401,8806613043418,8806613043425,8806613043432,8806613043449,8806613043456', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089515]대추엑스산|[M089512]생강엑스산|[M082727]감초엑스산|[M089568]반하엑스산|[M090093]작약엑스산|[M051650]인삼엑스산|[M089535]황금엑스산|[M089525]계지엑스산|[M089498]시호엑스산', '함량_원료성분원문': '총량 : 1회 용량(2.52그램) 중|성분명 : 시호엑스산|분량 : 0.42|단위 : 그램|규격 : 생규|성분정보 : 시호로서 2.50g;총량 : 1회 용량(2.52그램) 중|성분명 : 계지엑스산|분량 : 0.04|단위 : 그램|규격 : 생규|성분정보 : 계지로서 1.25g;총량 : 1회 용량(2.52그램) 중|성분명 : 황금엑스산|분량 : 0.56|단위 : 그램|규격 : 생규|성분정보 : 황금으로서 1.25g;총량 : 1회 용량(2.52그램) 중|성분명 : 인삼엑스산|분량 : 0.30|단위 : 그램|규격 : 생규|성분정보 : 인삼으로서 1.25g;총량 : 1회 용량(2.52그램) 중|성분명 : 작약엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 작약으로서 1.25g;총량 : 1회 용량(2.52그램) 중|성분명 : 반하엑스산|분량 : 0.32|단위 : 그램|규격 : 생규|성분정보 : 반하로서 1.25g;총량 : 1회 용량(2.52그램) 중|성분명 : 감초엑스산|분량 : 0.17|단위 : 그램|규격 : 생규|성분정보 : 감초로서 0.63g;총량 : 1회 용량(2.52그램) 중|성분명 : 생강엑스산|분량 : 0.03|단위 : 그램|규격 : 생규|성분정보 : 생강으로서 0.50g;총량 : 1회 용량(2.52그램) 중|성분명 : 대추엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 대추로서 0.67g', '함량_총량기준': '1회 용량(2.52그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005622', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005622', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005623', 'ITEM_NAME': '경방시호소간탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초엑스산;향부자엑스산;지각엑스산;작약엑스산;천궁엑스산;진피엑스산;시호엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613012407,8806613012414,8806613012421,8806613012438,8806613012445,8806613012452,8806613012469,8806613043500,8806613043517,8806613043524,8806613043531,8806613043548,8806613043555', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M082727]감초엑스산|[M089589]향부자엑스산|[M089552]지각엑스산|[M090093]작약엑스산|[M089533]천궁엑스산|[M089506]진피엑스산|[M089498]시호엑스산', '함량_원료성분원문': '총량 : 1회 용량(2.46그램) 중|성분명 : 시호엑스산|분량 : 0.25|단위 : 그램|규격 : 생규|성분정보 : 시호로서 1.50 g;총량 : 1회 용량(2.46그램) 중|성분명 : 진피엑스산|분량 : 0.48|단위 : 그램|규격 : 생규|성분정보 : 진피로서 1.50 g;총량 : 1회 용량(2.46그램) 중|성분명 : 천궁엑스산|분량 : 0.43|단위 : 그램|규격 : 생규|성분정보 : 천궁으로서 1.25 g;총량 : 1회 용량(2.46그램) 중|성분명 : 작약엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 작약으로서 1.25 g;총량 : 1회 용량(2.46그램) 중|성분명 : 지각엑스산|분량 : 0.39|단위 : 그램|규격 : 생규|성분정보 : 지각으로서 1.25 g;총량 : 1회 용량(2.46그램) 중|성분명 : 향부자엑스산|분량 : 0.40|단위 : 그램|규격 : 생규|성분정보 : 향부자로서 1.25 g;총량 : 1회 용량(2.46그램) 중|성분명 : 감초엑스산|분량 : 0.17|단위 : 그램|규격 : 생규|성분정보 : 감초로서 0.63 g', '함량_총량기준': '1회 용량(2.46그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005623', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005623', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005624', 'ITEM_NAME': '경방시호청간탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초엑스산;길경엑스산;연교엑스산;청피엑스산;천궁엑스산;인삼엑스산;황금엑스산;치자엑스산;시호엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613012605,8806613012612,8806613012629,8806613012636,8806613012643,8806613012650,8806613012667,8806613043609,8806613043616,8806613043623,8806613043630,8806613043647,8806613043654', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M082727]감초엑스산|[M084832]길경엑스산|[M089560]연교엑스산|[M089586]청피엑스산|[M089533]천궁엑스산|[M051650]인삼엑스산|[M089535]황금엑스산|[M089503]치자엑스산|[M089498]시호엑스산', '함량_원료성분원문': '총량 : 1회 용량(3.54그램) 중|성분명 : 시호엑스산|분량 : 0.42|단위 : 그램|규격 : 생규|성분정보 : 시호로서 2.50 g;총량 : 1회 용량(3.54그램) 중|성분명 : 치자엑스산|분량 : 0.66|단위 : 그램|규격 : 생규|성분정보 : 치자로서 1.88 g;총량 : 1회 용량(3.54그램) 중|성분명 : 황금엑스산|분량 : 0.56|단위 : 그램|규격 : 생규|성분정보 : 황금으로서 1.25 g;총량 : 1회 용량(3.54그램) 중|성분명 : 인삼엑스산|분량 : 0.30|단위 : 그램|규격 : 생규|성분정보 : 인삼으로서 1.25 g;총량 : 1회 용량(3.54그램) 중|성분명 : 천궁엑스산|분량 : 0.43|단위 : 그램|규격 : 생규|성분정보 : 천궁으로서 1.25 g;총량 : 1회 용량(3.54그램) 중|성분명 : 청피엑스산|분량 : 0.39|단위 : 그램|규격 : 생규|성분정보 : 청피로서 1.25 g;총량 : 1회 용량(3.54그램) 중|성분명 : 연교엑스산|분량 : 0.18|단위 : 그램|규격 : 생규|성분정보 : 연교로서 1.00 g;총량 : 1회 용량(3.54그램) 중|성분명 : 길경엑스산|분량 : 0.43|단위 : 그램|규격 : 생규|성분정보 : 길경으로서 1.00 g;총량 : 1회 용량(3.54그램) 중|성분명 : 감초엑스산|분량 : 0.17|단위 : 그램|규격 : 생규|성분정보 : 감초로서 0.63 g', '함량_총량기준': '1회 용량(3.54그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005624', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005624', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005820', 'ITEM_NAME': '경방십전대보탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '작약;천궁;숙지황;감초;당귀;백출;복령;황기;계지;인삼', 'ENTP_NAME': '경방신약(주)', 'CHART': '적갈색의 과립제', 'CHANGE_DATE': '2020-04-09', 'BAR_CODE': '8806613013107,8806613013114', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040523]작약|[M040550]천궁|[M051364]숙지황|[M040006]감초|[M040070]당귀|[M040214]백출|[M040225]복령|[M040790]황기|[M050037]계지|[M040213]인삼', '함량_원료성분원문': '총량 : 1회3.0그램|성분명 : 인삼|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 계지|분량 : 1|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회3.0그램|성분명 : 황기|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 복령|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 백출|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 당귀|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 작약|분량 : 1|단위 : 그램|규격 : KP|성분정보 : 패오니플로린으로서 28.6밀리그램;총량 : 1회3.0그램|성분명 : 천궁|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 숙지황|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 감초|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : 글리시리진산으로서 22.5밀리그램', '함량_총량기준': '13.0', '수집URL': 'https://drug.hospitalk.net/item/200005820', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005820', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200707044', 'ITEM_NAME': '경방쌍화탕액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대추;생강;감초;육계;천궁;당귀;황기;숙지황;작약', 'ENTP_NAME': '경방신약(주)', 'CHART': '알루미늄 파우치에 충전된 흑갈색의 액제', 'CHANGE_DATE': '2023-01-16', 'BAR_CODE': '8806613013206,8806613013213', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040071]대추|[M050752]생강|[M040006]감초|[M050036]육계|[M040550]천궁|[M040070]당귀|[M040790]황기|[M051364]숙지황|[M040523]작약', '함량_원료성분원문': '총량 : 1회용량 1포(75mL) 중|성분명 : 작약|분량 : 3.13|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 1포(75mL) 중|성분명 : 숙지황|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 1포(75mL) 중|성분명 : 황기|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 1포(75mL) 중|성분명 : 당귀|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 1포(75mL) 중|성분명 : 천궁|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 1포(75mL) 중|성분명 : 육계|분량 : 0.94|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 1포(75mL) 중|성분명 : 감초|분량 : 0.94|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 1포(75mL) 중|성분명 : 생강|분량 : 0.50|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회용량 1포(75mL) 중|성분명 : 대추|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1회용량 1포(75mL) 중', '수집URL': 'https://drug.hospitalk.net/item/200707044', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200707044', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005841', 'ITEM_NAME': '경방쌍화탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '생강;작약;황기;대추;당귀;감초;육계;천궁;숙지황', 'ENTP_NAME': '경방신약(주)', 'CHART': '담갈색의 과립제', 'CHANGE_DATE': '2021-07-22', 'BAR_CODE': '8806613013305,8806613013312', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050752]생강|[M040523]작약|[M040790]황기|[M040071]대추|[M040070]당귀|[M040006]감초|[M050036]육계|[M040550]천궁|[M051364]숙지황', '함량_원료성분원문': '총량 : 1회3.0그램|성분명 : 숙지황|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 천궁|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 육계|분량 : 0.94|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 감초|분량 : 0.94|단위 : 그램|규격 : KP|성분정보 : 글리시리진산으로서 18.8밀리그램;총량 : 1회3.0그램|성분명 : 당귀|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 대추|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 황기|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 작약|분량 : 3.13|단위 : 그램|규격 : KP|성분정보 : 패오니플로린으로서 62.6밀리그램;총량 : 1회3.0그램|성분명 : 생강|분량 : 0.50|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '13.0', '수집URL': 'https://drug.hospitalk.net/item/200005841', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005841', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005626', 'ITEM_NAME': '경방연교패독산산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '방풍엑스산;강활엑스산;독활엑스산;시호엑스산;천궁엑스산;지각엑스산;형개엑스산;금은화엑스산;연교엑스산;길경엑스산;복령엑스산;감초엑스산;박하엑스산;생강엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613014005,8806613014012,8806613014029,8806613014036,8806613014043,8806613014050,8806613014067,8806613014074,8806613043807,8806613043814,8806613043821,8806613043838,8806613043845,8806613043852', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089564]방풍엑스산|[M089546]강활엑스산|[M089547]독활엑스산|[M089498]시호엑스산|[M089533]천궁엑스산|[M089552]지각엑스산|[M089563]형개엑스산|[M089561]금은화엑스산|[M089560]연교엑스산|[M084832]길경엑스산|[M089528]복령엑스산|[M082727]감초엑스산|[M089555]박하엑스산|[M089512]생강엑스산', '함량_원료성분원문': '총량 : 1회 용량(2.89그램) 중|성분명 : 연교엑스산|분량 : 0.16|단위 : 그램|규격 : 생규|성분정보 : 연교로서 0.88 g;총량 : 1회 용량(2.89그램) 중|성분명 : 길경엑스산|분량 : 0.38|단위 : 그램|규격 : 생규|성분정보 : 길경으로서 0.88 g;총량 : 1회 용량(2.89그램) 중|성분명 : 복령엑스산|분량 : 0.02|단위 : 그램|규격 : 생규|성분정보 : 복령으로서 0.88 g;총량 : 1회 용량(2.89그램) 중|성분명 : 감초엑스산|분량 : 0.24|단위 : 그램|규격 : 생규|성분정보 : 감초로서 0.88 g;총량 : 1회 용량(2.89그램) 중|성분명 : 박하엑스산|분량 : 0.18|단위 : 그램|규격 : 생규|성분정보 : 박하로서 0.88 g;총량 : 1회 용량(2.89그램) 중|성분명 : 생강엑스산|분량 : 0.03|단위 : 그램|규격 : 생규|성분정보 : 생강으로서 0.50 g;총량 : 1회 용량(2.89그램) 중|성분명 : 금은화엑스산|분량 : 0.25|단위 : 그램|규격 : 생규|성분정보 : 금은화로서 0.88 g;총량 : 1회 용량(2.89그램) 중|성분명 : 형개엑스산|분량 : 0.12|단위 : 그램|규격 : 생규|성분정보 : 형개로서 0.88 g;총량 : 1회 용량(2.89그램) 중|성분명 : 방풍엑스산|분량 : 0.30|단위 : 그램|규격 : 생규|성분정보 : 방풍으로서 0.88 g;총량 : 1회 용량(2.89그램) 중|성분명 : 강활엑스산|분량 : 0.25|단위 : 그램|규격 : 생규|성분정보 : 강활로서 0.88 g;총량 : 1회 용량(2.89그램) 중|성분명 : 독활엑스산|분량 : 0.24|단위 : 그램|규격 : 생규|성분정보 : 독활로서 0.88 g;총량 : 1회 용량(2.89그램) 중|성분명 : 시호엑스산|분량 : 0.15|단위 : 그램|규격 : 생규|성분정보 : 시호로서 0.88 g;총량 : 1회 용량(2.89그램) 중|성분명 : 천궁엑스산|분량 : 0.30|단위 : 그램|규격 : 생규|성분정보 : 천궁으로서 0.88 g;총량 : 1회 용량(2.89그램) 중|성분명 : 지각엑스산|분량 : 0.27|단위 : 그램|규격 : 생규|성분정보 : 지각으로서 0.88 g', '함량_총량기준': '1회 용량(2.89그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005626', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005626', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201804617', 'ITEM_NAME': '경방연교패독산연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '지각연조엑스(1.5~1.8→1);천궁연조엑스(2.1~2.6→1);시호연조엑스(3.6~4.4→1);독활연조엑스(3.0~3.7→1);강활연조엑스(2.6~3.2→1);방풍연조엑스(2.5~3.1→1);형개연조엑스(4.3~5.9→1);금은화연조엑스(2.9~3.6→1);연교연조엑스(3.6~4.4→1);길경연조엑스(2.3~2.8→1);복령연조엑스(5.8∼7.8→1);감초연조엑스(2.1~2.5→1);박하연조엑스(3.2~4.0→1);생강연조엑스(5.1~6.9→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2020-07-09', 'BAR_CODE': '8806613050409,8806613050416,8806613050423,8806613050430', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M264376]지각연조엑스(1.5~1.8→1)|[M268189]천궁연조엑스(2.1~2.6→1)|[M266614]시호연조엑스(3.6~4.4→1)|[M268535]독활연조엑스(3.0~3.7→1)|[M266596]강활연조엑스(2.6~3.2→1)|[M266597]방풍연조엑스(2.5~3.1→1)|[M268534]형개연조엑스(4.3~5.9→1)|[M268194]금은화연조엑스(2.9~3.6→1)|[M266612]연교연조엑스(3.6~4.4→1)|[M262500]길경연조엑스(2.3~2.8→1)|[M268185]복령연조엑스(5.8∼7.8→1)|[M268186]감초연조엑스(2.1~2.5→1)|[M268536]박하연조엑스(3.2~4.0→1)|[M268065]생강연조엑스(5.1~6.9→1)', '함량_원료성분원문': '총량 : 1회용량(10g/포)|성분명 : 연교연조엑스(3.6~4.4→1)|분량 : 220.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포)|성분명 : 길경연조엑스(2.3~2.8→1)|분량 : 343.2|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포)|성분명 : 복령연조엑스(5.8∼7.8→1)|분량 : 132.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포)|성분명 : 감초연조엑스(2.1~2.5→1)|분량 : 387.2|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포)|성분명 : 박하연조엑스(3.2~4.0→1)|분량 : 246.4|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포)|성분명 : 생강연조엑스(5.1~6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포)|성분명 : 금은화연조엑스(2.9~3.6→1)|분량 : 272.8|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포)|성분명 : 형개연조엑스(4.3~5.9→1)|분량 : 176.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포)|성분명 : 방풍연조엑스(2.5~3.1→1)|분량 : 316.8|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포)|성분명 : 강활연조엑스(2.6~3.2→1)|분량 : 308.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포)|성분명 : 독활연조엑스(3.0~3.7→1)|분량 : 264.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포)|성분명 : 시호연조엑스(3.6~4.4→1)|분량 : 220.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포)|성분명 : 천궁연조엑스(2.1~2.6→1)|분량 : 378.4|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포)|성분명 : 지각연조엑스(1.5~1.8→1)|분량 : 545.6|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1회용량(10g/포)', '수집URL': 'https://drug.hospitalk.net/item/201804617', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201804617', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202500629', 'ITEM_NAME': '경방영선제통음시럽', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '강활;길경;당귀;독활;마황;방풍;백지;감초;황금주자;형개;갈근;승마;위령선;작약;지실;창출;천궁', 'ENTP_NAME': '경방신약(주)', 'CHART': '알루미늄 포에 충전된 갈색의 시럽', 'CHANGE_DATE': '2026-01-08', 'BAR_CODE': '8806613072302,8806613072319,8806613072326', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050022]강활|[M040048]길경|[M040070]당귀|[M050227]독활|[M040135]마황|[M040205]방풍|[M040216]백지|[M040006]감초|[M275882]황금주자|[M051936]형개|[M040004]갈근|[M040329]승마|[M083244]위령선|[M040523]작약|[M040536]지실|[M040548]창출|[M040550]천궁', '함량_원료성분원문': '총량 : 1포20그램|성분명 : 갈근|분량 : 625.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 승마|분량 : 375.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 위령선|분량 : 625.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포20그램|성분명 : 작약|분량 : 1,250.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 지실|분량 : 625.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 창출|분량 : 625.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 천궁|분량 : 625.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 형개|분량 : 625.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 황금주자|분량 : 625.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1포20그램|성분명 : 감초|분량 : 375.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 강활|분량 : 625.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 길경|분량 : 625.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 당귀|분량 : 375.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 독활|분량 : 625.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 마황|분량 : 1,250.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 방풍|분량 : 625.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 백지|분량 : 625.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '120', '수집URL': 'https://drug.hospitalk.net/item/202500629', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202500629', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005628', 'ITEM_NAME': '경방오적산산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '진피엑스산;후박엑스산;길경엑스산;지각엑스산;당귀엑스산;건강엑스산;작약엑스산;마황엑스산;생강엑스산;창출엑스산;복령엑스산;천궁엑스산;백지엑스산;반하엑스산;육계엑스산;감초엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613014708,8806613014715,8806613014722,8806613014739,8806613014746,8806613014753,8806613014760,8806613014777,8806613044002,8806613044019,8806613044026,8806613044033,8806613044040,8806613044057', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089506]진피엑스산|[M089507]후박엑스산|[M084832]길경엑스산|[M089552]지각엑스산|[M089119]당귀엑스산|[M089572]건강엑스산|[M090093]작약엑스산|[M089573]마황엑스산|[M089512]생강엑스산|[M089505]창출엑스산|[M089528]복령엑스산|[M089533]천궁엑스산|[M089600]백지엑스산|[M089568]반하엑스산|[M089617]육계엑스산|[M082727]감초엑스산', '함량_원료성분원문': '총량 : 1회 용량(4.36그램) 중|성분명 : 창출엑스산|분량 : 0.95|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 복령엑스산|분량 : 0.02|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 천궁엑스산|분량 : 0.30|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 백지엑스산|분량 : 0.31|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 반하엑스산|분량 : 0.22|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 육계엑스산|분량 : 0.05|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 감초엑스산|분량 : 0.20|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 생강엑스산|분량 : 0.03|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 마황엑스산|분량 : 0.20|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 진피엑스산|분량 : 0.40|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 후박엑스산|분량 : 0.08|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 길경엑스산|분량 : 0.43|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 지각엑스산|분량 : 0.31|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 당귀엑스산|분량 : 0.37|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 건강엑스산|분량 : 0.22|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(4.36그램) 중|성분명 : 작약엑스산|분량 : 0.27|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '1회 용량(4.36그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005628', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005628', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201800909', 'ITEM_NAME': '경방오적산연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '진피연조엑스(2.3~2.8→1);후박연조엑스(5.4~7.4→1);길경 연조엑스(2.3~2.8→1);지각 연조엑스(1.5~1.8→1);당귀연조엑스(2.8~3.4→1);건강연조엑스(2.9~3.6→1);작약 연조엑스(2.8~3.4→1);마황연조엑스(3.8~5.1→1);생강 연조엑스(5.1~6.9→1);창출연조엑스(2.9~3.6→1);복령연조엑스(5.8~7.8→1);천궁연조엑스(2.1~2.6→1);백지연조엑스(3.6~4.4→1);반하연조엑스(0.7~0.8→1);육계연조엑스(6.9~10.4→1);감초 연조엑스(2.1∼2.5→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2020-07-21', 'BAR_CODE': '8806613048703,8806613048710,8806613048727', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M266591]진피연조엑스(2.3~2.8→1)|[M279185]후박연조엑스(5.4~7.4→1)|[M116712]길경 연조엑스(2.3~2.8→1)|[M117331]지각 연조엑스(1.5~1.8→1)|[M279186]당귀연조엑스(2.8~3.4→1)|[M266876]건강연조엑스(2.9~3.6→1)|[M117955]작약 연조엑스(2.8~3.4→1)|[M279180]마황연조엑스(3.8~5.1→1)|[M273014]생강 연조엑스(5.1~6.9→1)|[M266600]창출연조엑스(2.9~3.6→1)|[M279187]복령연조엑스(5.8~7.8→1)|[M279188]천궁연조엑스(2.1~2.6→1)|[M266599]백지연조엑스(3.6~4.4→1)|[M279189]반하연조엑스(0.7~0.8→1)|[M279190]육계연조엑스(6.9~10.4→1) |[M272009]감초 연조엑스(2.1∼2.5→1)', '함량_원료성분원문': '총량 : |성분명 : 창출연조엑스(2.9~3.6→1)|분량 : 775.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 복령연조엑스(5.8~7.8→1)|분량 : 150.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 천궁연조엑스(2.1~2.6→1)|분량 : 378.4|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 백지연조엑스(3.6~4.4→1)|분량 : 220.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 반하연조엑스(0.7~0.8→1)|분량 : 1,223.2|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 육계연조엑스(6.9~10.4→1) |분량 : 105.6|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 감초 연조엑스(2.1∼2.5→1)|분량 : 330.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 생강 연조엑스(5.1~6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 마황연조엑스(3.8~5.1→1)|분량 : 287.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 진피연조엑스(2.3~2.8→1)|분량 : 500.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 후박연조엑스(5.4~7.4→1)|분량 : 160.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 길경 연조엑스(2.3~2.8→1)|분량 : 390.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 지각 연조엑스(1.5~1.8→1)|분량 : 620.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 당귀연조엑스(2.8~3.4→1)|분량 : 330.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 건강연조엑스(2.9~3.6→1)|분량 : 310.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : |성분명 : 작약 연조엑스(2.8~3.4→1)|분량 : 330.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '미기재', '수집URL': 'https://drug.hospitalk.net/item/201800909', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201800909', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201605386', 'ITEM_NAME': '경방오적산정(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '작약연조엑스(2.8～3.4→1);건강연조엑스(2.9～3.6→1);당귀연조엑스(2.8～3.4→1);지각연조엑스(1.5∼1.8→1);길경연조엑스(2.3∼2.8→1);후박연조엑스(5.4～7.4→1);진피연조엑스(2.3～2.8→1);마황연조엑스(3.8∼5.1→1);생강연조엑스(5.1～6.9→1);창출연조엑스(2.9～3.6→1);복령연조엑스(5.8∼7.8→1);천궁연조엑스(2.1～2.6→1);백지연조엑스(3.6∼4.4→1);반하연조엑스(0.7∼0.8→1);육계연조엑스(6.9∼10.4→1);감초연조엑스(2.1∼2.5→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 장방형 코팅정제', 'CHANGE_DATE': '2021-02-19', 'BAR_CODE': '8806613047508,8806613047515,8806613047522', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M280496]작약연조엑스(2.8～3.4→1)|[M280495]건강연조엑스(2.9～3.6→1)|[M280494]당귀연조엑스(2.8～3.4→1)|[M280493]지각연조엑스(1.5∼1.8→1)|[M280492]길경연조엑스(2.3∼2.8→1)|[M280491]후박연조엑스(5.4～7.4→1)|[M280490]진피연조엑스(2.3～2.8→1)|[M280489]마황연조엑스(3.8∼5.1→1)|[M280503]생강연조엑스(5.1～6.9→1)|[M280488]창출연조엑스(2.9～3.6→1)|[M280497]복령연조엑스(5.8∼7.8→1)|[M280498]천궁연조엑스(2.1～2.6→1)|[M280499]백지연조엑스(3.6∼4.4→1)|[M280500]반하연조엑스(0.7∼0.8→1)|[M280501]육계연조엑스(6.9∼10.4→1)|[M280502]감초연조엑스(2.1∼2.5→1)', '함량_원료성분원문': '총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 창출연조엑스(2.9～3.6→1)|분량 : 775.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 복령연조엑스(5.8∼7.8→1)|분량 : 150.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 천궁연조엑스(2.1～2.6→1)|분량 : 378.4|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 백지연조엑스(3.6∼4.4→1)|분량 : 220.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 반하연조엑스(0.7∼0.8→1)|분량 : 1223.2|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 육계연조엑스(6.9∼10.4→1)|분량 : 105.6|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 감초연조엑스(2.1∼2.5→1)|분량 : 330.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 생강연조엑스(5.1～6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 마황연조엑스(3.8∼5.1→1)|분량 : 287.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 진피연조엑스(2.3～2.8→1)|분량 : 500.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 후박연조엑스(5.4～7.4→1)|분량 : 160.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 길경연조엑스(2.3∼2.8→1)|분량 : 390.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 지각연조엑스(1.5∼1.8→1)|분량 : 620.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 당귀연조엑스(2.8～3.4→1)|분량 : 330.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 건강연조엑스(2.9～3.6→1)|분량 : 310.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량 (850 mg/정 × 4 정)|성분명 : 작약연조엑스(2.8～3.4→1)|분량 : 330.0|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회 용량 (850 mg/정 × 4 정)', '수집URL': 'https://drug.hospitalk.net/item/201605386', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201605386', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201908637', 'ITEM_NAME': '경방우황청심원(사향대체물질l-무스콘함유)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '용뇌;백렴;건강;l-무스콘;인삼;포황;신곡;육계;대두황권;아교;작약;영양각;우황;감초;산약;맥문동;당귀;방풍;백출;황금;시호;길경;행인;복령;천궁', 'ENTP_NAME': '경방신약(주)', 'CHART': '금박을 환의한 암갈색의 환제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806613054506,8806613054513,8806613054520', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051197]용뇌|[M050541]백렴|[M040007]건강|[M251442]l-무스콘|[M051291]인삼|[M090765]포황|[M050891]신곡|[M050036]육계|[M050191]대두황권|[M050905]아교|[M040523]작약|[M051133]영양각|[M040478]우황|[M040006]감초|[M040258]산약|[M040139]맥문동|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040789]황금|[M040336]시호|[M040048]길경|[M040769]행인|[M040225]복령|[M040550]천궁', '함량_원료성분원문': '총량 : 1회3.75그램|성분명 : 산약|분량 : 282.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 맥문동|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 당귀|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 방풍|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 백출|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 황금|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 시호|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 길경|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 행인|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 복령|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 천궁|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 감초|분량 : 202.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 우황|분량 : 14.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 영양각|분량 : 35.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1회3.75그램|성분명 : 용뇌|분량 : 41.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1회3.75그램|성분명 : 백렴|분량 : 30.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1회3.75그램|성분명 : 건강|분량 : 30.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : l-무스콘|분량 : 0.075|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 인삼|분량 : 97.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 포황|분량 : 100.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1회3.75그램|성분명 : 신곡|분량 : 100.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1회3.75그램|성분명 : 육계|분량 : 70.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.75그램|성분명 : 대두황권|분량 : 70.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1회3.75그램|성분명 : 아교|분량 : 70.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1회3.75그램|성분명 : 작약|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '13.75', '수집URL': 'https://drug.hospitalk.net/item/201908637', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201908637', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202501103', 'ITEM_NAME': '경방우황청심원액(사향대체물질엘-무스콘함유)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': 'l-무스콘;백렴;건강;산약;포황;신곡;대두황권;육계;아교;작약;맥문동;용뇌;영양각;인삼;감초;황금;당귀;방풍;백출;시호;복령;길경;행인;천궁;우황', 'ENTP_NAME': '경방신약(주)', 'CHART': '특이한 방향성이 있는 갈색의 불투명한 액제.', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806613072708,8806613072715', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M251442]l-무스콘|[M050541]백렴|[M040007]건강|[M040258]산약|[M090765]포황|[M050891]신곡|[M050191]대두황권|[M050036]육계|[M050905]아교|[M040523]작약|[M040139]맥문동|[M051197]용뇌|[M051133]영양각|[M051291]인삼|[M040006]감초|[M040789]황금|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040336]시호|[M040225]복령|[M040048]길경|[M040769]행인|[M040550]천궁|[M040478]우황', '함량_원료성분원문': '총량 : 1병50밀리리터|성분명 : 감초|분량 : 202|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 황금|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 당귀|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 방풍|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 백출|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 시호|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 복령|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 길경|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 행인|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 천궁|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 우황|분량 : 14|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 인삼|분량 : 97|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 영양각|분량 : 35|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 용뇌|분량 : 41|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : l-무스콘|분량 : 75|단위 : 마이크로그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 백렴|분량 : 30|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 건강|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 산약|분량 : 282|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 포황|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 신곡|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 대두황권|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 육계|분량 : 70|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 아교|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 작약|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 맥문동|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '150', '수집URL': 'https://drug.hospitalk.net/item/202501103', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202501103', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202501104', 'ITEM_NAME': '경방우황청심원현탁액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건강;백렴;용뇌;사향;인삼;포황;신곡;대두황권;육계;아교;작약;영양각;우황;감초;산약;맥문동;황금;당귀;방풍;백출;시호;복령;길경;행인;천궁', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색유리병에 든 특이한 방향성이 있는 갈색의 불투명한 현탁제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806613072807,8806613072814', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040007]건강|[M050541]백렴|[M051197]용뇌|[M040253]사향|[M051291]인삼|[M090765]포황|[M050891]신곡|[M050191]대두황권|[M050036]육계|[M050905]아교|[M040523]작약|[M051133]영양각|[M040478]우황|[M040006]감초|[M040258]산약|[M040139]맥문동|[M040789]황금|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040336]시호|[M040225]복령|[M040048]길경|[M040769]행인|[M040550]천궁', '함량_원료성분원문': '총량 : 1병50밀리리터|성분명 : 산약|분량 : 282|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 맥문동|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 황금|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 당귀|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 방풍|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 백출|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 시호|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 복령|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 길경|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 행인|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 천궁|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 감초|분량 : 202|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 우황|분량 : 14|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 영양각|분량 : 35|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 사향|분량 : 5|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 용뇌|분량 : 41|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 백렴|분량 : 30|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 건강|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 인삼|분량 : 97|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 포황|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 신곡|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 대두황권|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 육계|분량 : 70|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 아교|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 작약|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '150', '수집URL': 'https://drug.hospitalk.net/item/202501104', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202501104', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200404349', 'ITEM_NAME': '경방우황포룡환', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '천축황;우담남성;호박;진주;사향;우황', 'ENTP_NAME': '경방신약(주)', 'CHART': '흑갈색의 내용물에 금박을 입힌 환제', 'CHANGE_DATE': '2010-04-09', 'BAR_CODE': '8806613015200,8806613015217', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051385]천축황|[M051206]우담남성|[M051946]호박|[M051366]진주|[M040253]사향|[M040478]우황', '함량_원료성분원문': '총량 : 1환 중 200밀리그램|성분명 : 우황|분량 : 3.1|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환 중 200밀리그램|성분명 : 사향|분량 : 6.3|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환 중 200밀리그램|성분명 : 진주|분량 : 6.3|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환 중 200밀리그램|성분명 : 호박|분량 : 6.3|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환 중 200밀리그램|성분명 : 우담남성|분량 : 63.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환 중 200밀리그램|성분명 : 천축황|분량 : 31.0|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1환 중 200밀리그램', '수집URL': 'https://drug.hospitalk.net/item/200404349', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200404349', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005629', 'ITEM_NAME': '경방이중탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '인삼엑스산;백출엑스산;건강엑스산;감초엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613015903,8806613015910,8806613015927,8806613015934,8806613015941,8806613015958,8806613015965,8806613044101,8806613044118,8806613044125,8806613044132,8806613044149,8806613044156', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051650]인삼엑스산|[M089527]백출엑스산|[M089572]건강엑스산|[M082727]감초엑스산', '함량_원료성분원문': '총량 : 1회 용량(2.41그램) 중|성분명 : 인삼엑스산|분량 : 0.60|단위 : 그램|규격 : 생규|성분정보 : 인삼으로서 2.50 g;총량 : 1회 용량(2.41그램) 중|성분명 : 백출엑스산|분량 : 0.92|단위 : 그램|규격 : 생규|성분정보 : 백출로서 2.50 g;총량 : 1회 용량(2.41그램) 중|성분명 : 건강엑스산|분량 : 0.55|단위 : 그램|규격 : 생규|성분정보 : 건강으로서 2.50 g;총량 : 1회 용량(2.41그램) 중|성분명 : 감초엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 감초로서 1.25 g', '함량_총량기준': '1회 용량(2.41그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005629', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005629', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005653', 'ITEM_NAME': '경방이중탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초;건강;백출;인삼', 'ENTP_NAME': '경방신약(주)', 'CHART': '황갈색의 과립제', 'CHANGE_DATE': '2020-02-28', 'BAR_CODE': '8806613016009,8806613016016', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040006]감초|[M040007]건강|[M040214]백출|[M051291]인삼', '함량_원료성분원문': '총량 : 1회 용량(3.0그램) 중|성분명 : 인삼|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : 진세노사이드Rb1으로서 2.0밀리그램;총량 : 1회 용량(3.0그램) 중|성분명 : 백출|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0그램) 중|성분명 : 건강|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3.0그램) 중|성분명 : 감초|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : 글리시리진산으로서 25.0밀리그램', '함량_총량기준': '1회 용량(3.0그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005653', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005653', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202200734', 'ITEM_NAME': '경방이진탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '생강 연조엑스(5.1~6.9→1);감초 연조엑스(2.1∼2.5→1);진피 연조엑스(2.3~2.8→1);복령 연조엑스(5.8∼7.8→1);반하 연조엑스(0.7∼0.8→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806613067506,8806613067513,8806613067520', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M273014]생강 연조엑스(5.1~6.9→1)|[M272009]감초 연조엑스(2.1∼2.5→1)|[M117835]진피 연조엑스(2.3~2.8→1)|[M272852]복령 연조엑스(5.8∼7.8→1)|[M272755]반하 연조엑스(0.7∼0.8→1)', '함량_원료성분원문': '총량 : 1회용량(10g/포) 중|성분명 : 반하 연조엑스(0.7∼0.8→1)|분량 : 3475.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포) 중|성분명 : 복령 연조엑스(5.8∼7.8→1)|분량 : 187.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포) 중|성분명 : 진피 연조엑스(2.3~2.8→1)|분량 : 500.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포) 중|성분명 : 감초 연조엑스(2.1∼2.5→1)|분량 : 277.2|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회용량(10g/포) 중|성분명 : 생강 연조엑스(5.1~6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1회용량(10g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/202200734', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202200734', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201604953', 'ITEM_NAME': '경방이진탕정(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '생강연조엑스(5.1～6.9→1);감초연조엑스(2.1∼2.5→1);진피연조엑스(2.3～2.8→1);복령연조엑스(5.8∼7.8→1);반하연조엑스(0.7∼0.8→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '적갈색의 장방형 필름코팅정제', 'CHANGE_DATE': '2026-10-16', 'BAR_CODE': '8806613047102,8806613047119,8806613047126,8806613047133', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M280426]생강연조엑스(5.1～6.9→1)|[M280425]감초연조엑스(2.1∼2.5→1)|[M280423]진피연조엑스(2.3～2.8→1)|[M280430]복령연조엑스(5.8∼7.8→1)|[M280429]반하연조엑스(0.7∼0.8→1)', '함량_원료성분원문': '총량 : 1회 용량(550 mg/정 x 2 정) 중|성분명 : 반하연조엑스(0.7∼0.8→1)|분량 : 3475.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(550 mg/정 x 2 정) 중|성분명 : 복령연조엑스(5.8∼7.8→1)|분량 : 187.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(550 mg/정 x 2 정) 중|성분명 : 진피연조엑스(2.3～2.8→1)|분량 : 500.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(550 mg/정 x 2 정) 중|성분명 : 감초연조엑스(2.1∼2.5→1)|분량 : 277.2|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(550 mg/정 x 2 정) 중|성분명 : 생강연조엑스(5.1～6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회 용량(550 mg/정 x 2 정) 중', '수집URL': 'https://drug.hospitalk.net/item/201604953', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201604953', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005634', 'ITEM_NAME': '경방자음강화탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '황백엑스산;지모엑스산;진피엑스산;생지황엑스산;맥문동엑스산;백출엑스산;숙지황엑스산;당귀엑스산;생강엑스산;대추엑스산;감초엑스산;작약엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613016801,8806613016818,8806613016825,8806613016832,8806613016849,8806613016856,8806613016863,8806613016870,8806613044606,8806613044613,8806613044620,8806613044637,8806613044644,8806613044651', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M085093]황백엑스산|[M089548]지모엑스산|[M089506]진피엑스산|[M089524]생지황엑스산|[M089553]맥문동엑스산|[M089527]백출엑스산|[M089536]숙지황엑스산|[M089119]당귀엑스산|[M089512]생강엑스산|[M089515]대추엑스산|[M082727]감초엑스산|[M090093]작약엑스산', '함량_원료성분원문': '총량 : 1회 용량(3.83그램) 중|성분명 : 작약엑스산|분량 : 0.44|단위 : 그램|규격 : 생규|성분정보 : 작약으로서 1.63g;총량 : 1회 용량(3.83그램) 중|성분명 : 감초엑스산|분량 : 0.17|단위 : 그램|규격 : 생규|성분정보 : 감초로서 0.63g;총량 : 1회 용량(3.83그램) 중|성분명 : 대추엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 대추로서 0.67g;총량 : 1회 용량(3.83그램) 중|성분명 : 생강엑스산|분량 : 0.03|단위 : 그램|규격 : 생규|성분정보 : 생강으로서 0.50g;총량 : 1회 용량(3.83그램) 중|성분명 : 당귀엑스산|분량 : 0.55|단위 : 그램|규격 : 생규|성분정보 : 당귀로서 1.50g;총량 : 1회 용량(3.83그램) 중|성분명 : 숙지황엑스산|분량 : 0.63|단위 : 그램|규격 : 생규|성분정보 : 숙지황으로서 1.25g;총량 : 1회 용량(3.83그램) 중|성분명 : 백출엑스산|분량 : 0.46|단위 : 그램|규격 : 생규|성분정보 : 백출로서 1.25g;총량 : 1회 용량(3.83그램) 중|성분명 : 맥문동엑스산|분량 : 0.38|단위 : 그램|규격 : 생규|성분정보 : 맥문동으로서 1.25g;총량 : 1회 용량(3.83그램) 중|성분명 : 생지황엑스산|분량 : 0.18|단위 : 그램|규격 : 생규|성분정보 : 생지황으로서 1.00g;총량 : 1회 용량(3.83그램) 중|성분명 : 진피엑스산|분량 : 0.28|단위 : 그램|규격 : 생규|성분정보 : 진피로서 0.88g;총량 : 1회 용량(3.83그램) 중|성분명 : 지모엑스산|분량 : 0.23|단위 : 그램|규격 : 생규|성분정보 : 지모로서 0.63g;총량 : 1회 용량(3.83그램) 중|성분명 : 황백엑스산|분량 : 0.14|단위 : 그램|규격 : 생규|성분정보 : 황백으로서 0.63g', '함량_총량기준': '1회 용량(3.83그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005634', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005634', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201901041', 'ITEM_NAME': '경방자음강화탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '황백연조엑스(1.9~2.3→1);지모연조엑스(2.4∼2.9→1);진피연조엑스(2.3~2.8→1);생지황연조엑스(3.6~4.9→1);맥문동연조엑스(2.4∼2.9→1);백출연조엑스(2.8~3.4→1);숙지황연조엑스(1.9∼2.3→1);작약연조엑스(2.8~3.4→1);감초연조엑스(2.1~2.5→1);대추연조엑스(1.8~2.2→1);생강연조엑스(5.1~6.9→1);당귀연조엑스(2.8~3.4→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2020-10-07', 'BAR_CODE': '8806613050607,8806613050614,8806613050621,8806613050638', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268981]황백연조엑스(1.9~2.3→1)|[M268980]지모연조엑스(2.4∼2.9→1)|[M266591]진피연조엑스(2.3~2.8→1)|[M268979]생지황연조엑스(3.6~4.9→1)|[M268978]맥문동연조엑스(2.4∼2.9→1)|[M268184]백출연조엑스(2.8~3.4→1)|[M266951]숙지황연조엑스(1.9∼2.3→1)|[M268068]작약연조엑스(2.8~3.4→1)|[M268186]감초연조엑스(2.1~2.5→1)|[M266595]대추연조엑스(1.8~2.2→1)|[M268065]생강연조엑스(5.1~6.9→1)|[M268188]당귀연조엑스(2.8~3.4→1)', '함량_원료성분원문': '총량 : 1회 용량(10g/포) 중|성분명 : 작약연조엑스(2.8~3.4→1)|분량 : 537.9|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 감초연조엑스(2.1~2.5→1)|분량 : 277.2|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 대추연조엑스(1.8~2.2→1)|분량 : 341.7|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 생강연조엑스(5.1~6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 당귀연조엑스(2.8~3.4→1)|분량 : 495.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 숙지황연조엑스(1.9∼2.3→1)|분량 : 600.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 백출연조엑스(2.8~3.4→1)|분량 : 412.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 맥문동연조엑스(2.4∼2.9→1)|분량 : 475.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 생지황연조엑스(3.6~4.9→1)|분량 : 240.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 진피연조엑스(2.3~2.8→1)|분량 : 352.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 지모연조엑스(2.4∼2.9→1)|분량 : 239.4|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 황백연조엑스(1.9~2.3→1)|분량 : 308.7|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1회 용량(10g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/201901041', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201901041', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005758', 'ITEM_NAME': '경방작약엑스산', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '작약', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 입상형 가루', 'CHANGE_DATE': '2019-02-28', 'BAR_CODE': '8806613016900,8806613016917,8806613016924,8806613016931,8806613016948,8806613016955', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040523]작약', '함량_원료성분원문': '총량 : 270밀리그램|성분명 : 작약|분량 : 1.0|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '270', '수집URL': 'https://drug.hospitalk.net/item/200005758', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005758', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201705472', 'ITEM_NAME': '경방작약엑스정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '작약 연조엑스(2.8~3.4→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '적갈색의 장방형 필름코팅정제', 'CHANGE_DATE': '2026-07-22', 'BAR_CODE': '8806613047805,8806613047812,8806613047829,8806613047836,8806613047843,8806613047850,8806613047867', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M117955]작약 연조엑스(2.8~3.4→1)', '함량_원료성분원문': '총량 : 1정(650mg) 중|성분명 : 작약 연조엑스(2.8~3.4→1)|분량 : 660.0|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1정(650mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201705472', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201705472', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005636', 'ITEM_NAME': '경방청상견통탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '맥문동엑스산;백지엑스산;당귀엑스산;천궁엑스산;방풍엑스산;독활엑스산;강활엑스산;창출엑스산;감초엑스산;세신엑스산;감국엑스산;만형자엑스산;황금엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613018607,8806613018614,8806613018621,8806613018638,8806613018645,8806613018652,8806613018669,8806613018676,8806613044804,8806613044811,8806613044828,8806613044835,8806613044842,8806613044859', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089553]맥문동엑스산|[M089600]백지엑스산|[M089119]당귀엑스산|[M089533]천궁엑스산|[M089564]방풍엑스산|[M089547]독활엑스산|[M089546]강활엑스산|[M089505]창출엑스산|[M082727]감초엑스산|[M089608]세신엑스산|[M089680]감국엑스산|[M089679]만형자엑스산|[M089535]황금엑스산', '함량_원료성분원문': '총량 : 1회 용량(4.66그램) 중|성분명 : 황금엑스산|분량 : 0.85|단위 : 그램|규격 : 생규|성분정보 : 황금으로서 1.88g;총량 : 1회 용량(4.66그램) 중|성분명 : 만형자엑스산|분량 : 0.07|단위 : 그램|규격 : 생규|성분정보 : 만형자로서 0.63g;총량 : 1회 용량(4.66그램) 중|성분명 : 감국엑스산|분량 : 0.27|단위 : 그램|규격 : 생규|성분정보 : 감국으로서 0.63g;총량 : 1회 용량(4.66그램) 중|성분명 : 세신엑스산|분량 : 0.05|단위 : 그램|규격 : 생규|성분정보 : 세신으로서 0.38g;총량 : 1회 용량(4.66그램) 중|성분명 : 감초엑스산|분량 : 0.10|단위 : 그램|규격 : 생규|성분정보 : 감초로서 0.38g;총량 : 1회 용량(4.66그램) 중|성분명 : 창출엑스산|분량 : 0.48|단위 : 그램|규격 : 생규|성분정보 : 창출로서 1.25g;총량 : 1회 용량(4.66그램) 중|성분명 : 강활엑스산|분량 : 0.36|단위 : 그램|규격 : 생규|성분정보 : 강활로서 1.25g;총량 : 1회 용량(4.66그램) 중|성분명 : 독활엑스산|분량 : 0.34|단위 : 그램|규격 : 생규|성분정보 : 독활로서 1.25g;총량 : 1회 용량(4.66그램) 중|성분명 : 방풍엑스산|분량 : 0.43|단위 : 그램|규격 : 생규|성분정보 : 방풍으로서 1.25g;총량 : 1회 용량(4.66그램) 중|성분명 : 천궁엑스산|분량 : 0.43|단위 : 그램|규격 : 생규|성분정보 : 천궁으로서 1.25g;총량 : 1회 용량(4.66그램) 중|성분명 : 당귀엑스산|분량 : 0.46|단위 : 그램|규격 : 생규|성분정보 : 당귀로서 1.25g;총량 : 1회 용량(4.66그램) 중|성분명 : 백지엑스산|분량 : 0.44|단위 : 그램|규격 : 생규|성분정보 : 백지로서 1.25g;총량 : 1회 용량(4.66그램) 중|성분명 : 맥문동엑스산|분량 : 0.38|단위 : 그램|규격 : 생규|성분정보 : 맥문동으로서 1.25g', '함량_총량기준': '1회 용량(4.66그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005636', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005636', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202106351', 'ITEM_NAME': '경방청상견통탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '방풍 연조엑스(2.5~3.1→1);천궁연조엑스(2.1~2.6→1);당귀연조엑스(2.8~3.4→1);백지 연조엑스(3.6~4.4→1);맥문동연조엑스(2.4~2.9→1);독활연조엑스(3.0~3.7→1);강활 연조엑스(2.6~3.2→1);창출 연조엑스(2.9~3.6→1);황금연조엑스(1.5~1.9→1);만형자연조엑스(10.0~16.7→1);감국연조엑스(4.6~6.2→1);세신연조엑스(3.5~4.3→1);감초연조엑스(2.1~2.5→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '알루미늄포에 충전된 갈색의 연조엑스', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806613067100,8806613067117,8806613067124', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M117841]방풍 연조엑스(2.5~3.1→1)|[M281407]천궁연조엑스(2.1~2.6→1)|[M281408]당귀연조엑스(2.8~3.4→1)|[M117843]백지 연조엑스(3.6~4.4→1)|[M281409]맥문동연조엑스(2.4~2.9→1)|[M268535]독활연조엑스(3.0~3.7→1)|[M117840]강활 연조엑스(2.6~3.2→1)|[M117844]창출 연조엑스(2.9~3.6→1)|[M117845]황금연조엑스(1.5~1.9→1)|[M281410]만형자연조엑스(10.0~16.7→1)|[M281411]감국연조엑스(4.6~6.2→1)|[M279182]세신연조엑스(3.5~4.3→1)|[M281412]감초연조엑스(2.1~2.5→1)', '함량_원료성분원문': '총량 : 1회 용량(10g/포)중|성분명 : 황금연조엑스(1.5~1.9→1)|분량 : 1,109.2|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 만형자연조엑스(10.0~16.7→1)|분량 : 50.4|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 감국연조엑스(4.6~6.2→1)|분량 : 119.7|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 세신연조엑스(3.5~4.3→1)|분량 : 98.8|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 감초연조엑스(2.1~2.5→1)|분량 : 167.2|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 창출 연조엑스(2.9~3.6→1)|분량 : 387.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 강활 연조엑스(2.6~3.2→1)|분량 : 437.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 독활연조엑스(3.0~3.7→1)|분량 : 375.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 방풍 연조엑스(2.5~3.1→1)|분량 : 450.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 천궁연조엑스(2.1~2.6→1)|분량 : 537.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 당귀연조엑스(2.8~3.4→1)|분량 : 412.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 백지 연조엑스(3.6~4.4→1)|분량 : 312.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 맥문동연조엑스(2.4~2.9→1)|분량 : 475.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1회 용량(10g/포)중', '수집URL': 'https://drug.hospitalk.net/item/202106351', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202106351', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005637', 'ITEM_NAME': '경방청서익기탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '인삼엑스산;백출엑스산;진피엑스산;신곡엑스산;택사엑스산;황백엑스산;승마엑스산;황기엑스산;감초엑스산;맥문동엑스산;청피엑스산;갈근엑스산;당귀엑스산;창출엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613018805,8806613018812,8806613018829,8806613018836,8806613018843,8806613018850,8806613018867,8806613044903,8806613044910,8806613044927,8806613044934,8806613044941,8806613044958', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051650]인삼엑스산|[M089527]백출엑스산|[M089506]진피엑스산|[M089584]신곡엑스산|[M089587]택사엑스산|[M085093]황백엑스산|[M089520]승마엑스산|[M089579]황기엑스산|[M082727]감초엑스산|[M089553]맥문동엑스산|[M089586]청피엑스산|[M089599]갈근엑스산|[M089119]당귀엑스산|[M089505]창출엑스산', '함량_원료성분원문': '총량 : 1회 용량(2.92그램) 중|성분명 : 창출엑스산|분량 : 0.71|단위 : 그램|규격 : 생규|성분정보 : 창출로서 1.88g;총량 : 1회 용량(2.92그램) 중|성분명 : 당귀엑스산|분량 : 0.14|단위 : 그램|규격 : 생규|성분정보 : 당귀로서 0.38g;총량 : 1회 용량(2.92그램) 중|성분명 : 갈근엑스산|분량 : 0.17|단위 : 그램|규격 : 생규|성분정보 : 갈근으로서 0.38g;총량 : 1회 용량(2.92그램) 중|성분명 : 청피엑스산|분량 : 0.12|단위 : 그램|규격 : 생규|성분정보 : 청피로서 0.38g;총량 : 1회 용량(2.92그램) 중|성분명 : 맥문동엑스산|분량 : 0.11|단위 : 그램|규격 : 생규|성분정보 : 맥문동으로서 0.38g;총량 : 1회 용량(2.92그램) 중|성분명 : 감초엑스산|분량 : 0.10|단위 : 그램|규격 : 생규|성분정보 : 감초로서 0.38g;총량 : 1회 용량(2.92그램) 중|성분명 : 황기엑스산|분량 : 0.27|단위 : 그램|규격 : 생규|성분정보 : 황기로서 1.25g;총량 : 1회 용량(2.92그램) 중|성분명 : 승마엑스산|분량 : 0.20|단위 : 그램|규격 : 생규|성분정보 : 승마로서 1.25g;총량 : 1회 용량(2.92그램) 중|성분명 : 인삼엑스산|분량 : 0.15|단위 : 그램|규격 : 생규|성분정보 : 인삼으로서 0.63g;총량 : 1회 용량(2.92그램) 중|성분명 : 백출엑스산|분량 : 0.23|단위 : 그램|규격 : 생규|성분정보 : 백출로서 0.63g;총량 : 1회 용량(2.92그램) 중|성분명 : 진피엑스산|분량 : 0.20|단위 : 그램|규격 : 생규|성분정보 : 진피로서 0.63g;총량 : 1회 용량(2.92그램) 중|성분명 : 신곡엑스산|분량 : 0.32|단위 : 그램|규격 : 생규|성분정보 : 신곡으로서 0.63g;총량 : 1회 용량(2.92그램) 중|성분명 : 택사엑스산|분량 : 0.11|단위 : 그램|규격 : 생규|성분정보 : 택사로서 0.63g;총량 : 1회 용량(2.92그램) 중|성분명 : 황백엑스산|분량 : 0.09|단위 : 그램|규격 : 생규|성분정보 : 황백으로서 0.38g', '함량_총량기준': '1회 용량(2.92그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005637', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005637', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202501235', 'ITEM_NAME': '경방청폐탕시럽', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '오미자;상백피;복령;맥문동;대추;당귀;길경;건강;황금;감초;절패모;진피;천문동;치자;행인', 'ENTP_NAME': '경방신약(주)', 'CHART': '알루미늄 포에 충전된 갈색의 시럽제', 'CHANGE_DATE': '2026-10-12', 'BAR_CODE': '8806613073002,8806613073019,8806613073026', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040445]오미자|[M040271]상백피|[M040225]복령|[M040139]맥문동|[M040071]대추|[M040070]당귀|[M040048]길경|[M040007]건강|[M040789]황금|[M040006]감초|[M201579]절패모|[M040538]진피|[M051380]천문동|[M040564]치자|[M040769]행인', '함량_원료성분원문': '총량 : 1포20그램|성분명 : 감초|분량 : 380.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 절패모|분량 : 1,250.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 진피|분량 : 1,250.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 천문동|분량 : 880.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 치자|분량 : 880.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 행인|분량 : 880.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 황금|분량 : 1,880.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 건강|분량 : 1,000.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 길경|분량 : 1,250.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 당귀|분량 : 880.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 대추|분량 : 670.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 맥문동|분량 : 880.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 복령|분량 : 1,250.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 상백피|분량 : 1,250.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포20그램|성분명 : 오미자|분량 : 110.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '120', '수집URL': 'https://drug.hospitalk.net/item/202501235', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202501235', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005639', 'ITEM_NAME': '경방팔물탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '당귀엑스산;천궁엑스산;작약엑스산;숙지황엑스산;감초엑스산;복령엑스산;백출엑스산;인삼엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613019604,8806613019611,8806613019628,8806613019635,8806613019642,8806613019659,8806613019666,8806613019673,8806613045108,8806613045115,8806613045122,8806613045139,8806613045146,8806613045153', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089119]당귀엑스산|[M089533]천궁엑스산|[M090093]작약엑스산|[M089536]숙지황엑스산|[M082727]감초엑스산|[M089528]복령엑스산|[M089527]백출엑스산|[M051650]인삼엑스산', '함량_원료성분원문': '총량 : 1회 용량 (3.59그램) 중|성분명 : 인삼엑스산|분량 : 0.36|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량 (3.59그램) 중|성분명 : 백출엑스산|분량 : 0.56|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량 (3.59그램) 중|성분명 : 복령엑스산|분량 : 0.03|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량 (3.59그램) 중|성분명 : 감초엑스산|분량 : 0.41|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량 (3.59그램) 중|성분명 : 숙지황엑스산|분량 : 0.75|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량 (3.59그램) 중|성분명 : 작약엑스산|분량 : 0.41|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량 (3.59그램) 중|성분명 : 천궁엑스산|분량 : 0.51|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량 (3.59그램) 중|성분명 : 당귀엑스산|분량 : 0.56|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '1회 용량 (3.59그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005639', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005639', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201803754', 'ITEM_NAME': '경방팔물탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '당귀연조엑스(2.8~3.4→1);천궁연조엑스(2.1~2.6→1);작약연조엑스(2.8~3.4→1);숙지황연조엑스(1.9∼2.3→1);감초연조엑스(2.1~2.5→1);복령연조엑스(5.8∼7.8→1);백출연조엑스(2.8~3.4→1);인삼연조엑스(3.2~4.0→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2020-10-30', 'BAR_CODE': '8806613049809,8806613049816,8806613049823,8806613049830', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268188]당귀연조엑스(2.8~3.4→1)|[M268189]천궁연조엑스(2.1~2.6→1)|[M268068]작약연조엑스(2.8~3.4→1)|[M266951]숙지황연조엑스(1.9∼2.3→1)|[M268186]감초연조엑스(2.1~2.5→1)|[M268185]복령연조엑스(5.8∼7.8→1)|[M268184]백출연조엑스(2.8~3.4→1)|[M266585]인삼연조엑스(3.2~4.0→1)', '함량_원료성분원문': '총량 : 1회 용량(10 g/포) 중|성분명 : 인삼연조엑스(3.2~4.0→1)|분량 : 420|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 백출연조엑스(2.8~3.4→1)|분량 : 495|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 복령연조엑스(5.8∼7.8→1)|분량 : 225|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 감초연조엑스(2.1~2.5→1)|분량 : 660|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 숙지황연조엑스(1.9∼2.3→1)|분량 : 720|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 작약연조엑스(2.8~3.4→1)|분량 : 495|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 천궁연조엑스(2.1~2.6→1)|분량 : 645|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 당귀연조엑스(2.8~3.4→1)|분량 : 495|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회 용량(10 g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/201803754', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201803754', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005835', 'ITEM_NAME': '경방팔미지황환엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '정제부자;육계;목단피;복령;택사;산약;산수유;숙지황', 'ENTP_NAME': '경방신약(주)', 'CHART': '황갈색의 과립제', 'CHANGE_DATE': '2021-10-22', 'BAR_CODE': '8806613019703,8806613019710', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M201585]정제부자|[M050036]육계|[M040185]목단피|[M040225]복령|[M040638]택사|[M040258]산약|[M040257]산수유|[M051364]숙지황', '함량_원료성분원문': '총량 : 1회3.0그램|성분명 : 숙지황|분량 : 2.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 산수유|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 산약|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 택사|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 복령|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 목단피|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 육계|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회3.0그램|성분명 : 정제부자|분량 : 0.33|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '13.0', '수집URL': 'https://drug.hospitalk.net/item/200005835', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005835', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201803161', 'ITEM_NAME': '경방평위산연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대추연조엑스(1.8~2.2→1);생강연조엑스(5.1~6.9→1);감초연조엑스(2.1∼2.5→1);후박연조엑스(5.4~7.4→1);진피연조엑스(2.3~2.8→1);창출연조엑스(2.9~3.6→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2020-08-03', 'BAR_CODE': '8806613049304,8806613049311,8806613049328', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M266595]대추연조엑스(1.8~2.2→1)|[M268065]생강연조엑스(5.1~6.9→1)|[M268064]감초연조엑스(2.1∼2.5→1)|[M279185]후박연조엑스(5.4~7.4→1)|[M266591]진피연조엑스(2.3~2.8→1)|[M266600]창출연조엑스(2.9~3.6→1)', '함량_원료성분원문': '총량 : 1회 용량(10g/포)중|성분명 : 창출연조엑스(2.9~3.6→1)|분량 : 775.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 진피연조엑스(2.3~2.8→1)|분량 : 700.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 후박연조엑스(5.4~7.4→1)|분량 : 200.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 감초연조엑스(2.1∼2.5→1)|분량 : 330.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 생강연조엑스(5.1~6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회 용량(10g/포)중|성분명 : 대추연조엑스(1.8~2.2→1)|분량 : 341.7|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1회 용량(10g/포)중', '수집URL': 'https://drug.hospitalk.net/item/201803161', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201803161', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201605093', 'ITEM_NAME': '경방평위산정(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대추연조엑스(1.8∼2.2→1);생강연조엑스(5.1～6.9→1);감초연조엑스(2.1∼2.5→1);후박연조엑스(5.4～7.4→1);진피연조엑스(2.3～2.8→1);창출연조엑스(2.9～3.6→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '적갈색의 장방형 필름코팅정제', 'CHANGE_DATE': '2026-10-16', 'BAR_CODE': '8806613047409,8806613047416,8806613047423', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M280427]대추연조엑스(1.8∼2.2→1)|[M280426]생강연조엑스(5.1～6.9→1)|[M280425]감초연조엑스(2.1∼2.5→1)|[M280424]후박연조엑스(5.4～7.4→1)|[M280423]진피연조엑스(2.3～2.8→1)|[M280422]창출연조엑스(2.9～3.6→1)', '함량_원료성분원문': '총량 : 1회분량(600 mg/정 x 3정) |성분명 : 창출연조엑스(2.9～3.6→1)|분량 : 775.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회분량(600 mg/정 x 3정) |성분명 : 진피연조엑스(2.3～2.8→1)|분량 : 700.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회분량(600 mg/정 x 3정) |성분명 : 후박연조엑스(5.4～7.4→1)|분량 : 200.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회분량(600 mg/정 x 3정) |성분명 : 감초연조엑스(2.1∼2.5→1)|분량 : 330.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회분량(600 mg/정 x 3정) |성분명 : 생강연조엑스(5.1～6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회분량(600 mg/정 x 3정) |성분명 : 대추연조엑스(1.8∼2.2→1)|분량 : 341.7|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회분량(600 mg/정 x 3정)', '수집URL': 'https://drug.hospitalk.net/item/201605093', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201605093', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005641', 'ITEM_NAME': '경방행소탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초엑스산;오미자엑스산;백출엑스산;절패모엑스산;반하엑스산;상백피엑스산;진피엑스산;자소엽엑스산;생강엑스산;행인엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613019901,8806613019918,8806613019925,8806613019932,8806613019949,8806613019956,8806613019963,8806613045306,8806613045313,8806613045320,8806613045337,8806613045344,8806613045351,8806613045368', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M082727]감초엑스산|[M089619]오미자엑스산|[M089527]백출엑스산|[M258338]절패모엑스산|[M089568]반하엑스산|[M258337]상백피엑스산|[M089506]진피엑스산|[M089623]자소엽엑스산|[M089512]생강엑스산|[M089575]행인엑스산', '함량_원료성분원문': '총량 : 1회 용량(2.48그램) 중|성분명 : 행인엑스산|분량 : 0.29|단위 : 그램|규격 : 생규|성분정보 : 행인으로서 1.25g;총량 : 1회 용량(2.48그램) 중|성분명 : 생강엑스산|분량 : 0.05|단위 : 그램|규격 : 생규|성분정보 : 생강으로서 0.83g;총량 : 1회 용량(2.48그램) 중|성분명 : 자소엽엑스산|분량 : 0.20|단위 : 그램|규격 : 생규|성분정보 : 자소엽으로서 1.25g;총량 : 1회 용량(2.48그램) 중|성분명 : 진피엑스산|분량 : 0.40|단위 : 그램|규격 : 생규|성분정보 : 진피로서 1.25g;총량 : 1회 용량(2.48그램) 중|성분명 : 상백피엑스산|분량 : 0.13|단위 : 그램|규격 : 생규|성분정보 : 상백피로서 1.25g;총량 : 1회 용량(2.48그램) 중|성분명 : 반하엑스산|분량 : 0.31|단위 : 그램|규격 : 생규|성분정보 : 반하로서 1.25g;총량 : 1회 용량(2.48그램) 중|성분명 : 절패모엑스산|분량 : 0.11|단위 : 그램|규격 : 생규|성분정보 : 절패모로서 1.25g;총량 : 1회 용량(2.48그램) 중|성분명 : 백출엑스산|분량 : 0.46|단위 : 그램|규격 : 생규|성분정보 : 백출로서 1.25g;총량 : 1회 용량(2.48그램) 중|성분명 : 오미자엑스산|분량 : 0.36|단위 : 그램|규격 : 생규|성분정보 : 오미자로서 1.25g;총량 : 1회 용량(2.48그램) 중|성분명 : 감초엑스산|분량 : 0.17|단위 : 그램|규격 : 생규|성분정보 : 감초로서 0.63g', '함량_총량기준': '1회 용량(2.48그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005641', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005641', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202106398', 'ITEM_NAME': '경방행소탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초 연조엑스(2.1∼2.5→1);오미자연조엑스(3.6∼4.4→1);백출 연조엑스(2.8∼3.4→1);절패모연조엑스(8.8∼14.7→1);반하 연조엑스(0.7∼0.8→1);상백피연조엑스(6.9∼10.4→1);진피연조엑스(2.3∼2.8→1);자소엽 연조엑스(2.7∼3.3→1);생강연조엑스(5.1∼6.9→1);행인연조엑스(3.4∼4.1→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '알루미늄포에 충전된 갈색의 연조엑스', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806613067209,8806613067216,8806613067223', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M272009]감초 연조엑스(2.1∼2.5→1)|[M281424]오미자연조엑스(3.6∼4.4→1)|[M272782]백출 연조엑스(2.8∼3.4→1)|[M281423]절패모연조엑스(8.8∼14.7→1)|[M272755]반하 연조엑스(0.7∼0.8→1)|[M281422]상백피연조엑스(6.9∼10.4→1)|[M281421]진피연조엑스(2.3∼2.8→1)|[M273975]자소엽 연조엑스(2.7∼3.3→1)|[M281425]생강연조엑스(5.1∼6.9→1)|[M268066]행인연조엑스(3.4∼4.1→1)', '함량_원료성분원문': '총량 : |성분명 : 행인연조엑스(3.4∼4.1→1)|분량 : 337.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : |성분명 : 생강연조엑스(5.1∼6.9→1)|분량 : 141.1|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : |성분명 : 자소엽 연조엑스(2.7∼3.3→1)|분량 : 425.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : |성분명 : 진피연조엑스(2.3∼2.8→1)|분량 : 500.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : |성분명 : 상백피연조엑스(6.9∼10.4→1)|분량 : 150.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : |성분명 : 반하 연조엑스(0.7∼0.8→1)|분량 : 1,737.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : |성분명 : 절패모연조엑스(8.8∼14.7→1)|분량 : 112.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : |성분명 : 백출 연조엑스(2.8∼3.4→1)|분량 : 412.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : |성분명 : 오미자연조엑스(3.6∼4.4→1)|분량 : 312.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : |성분명 : 감초 연조엑스(2.1∼2.5→1)|분량 : 277.2|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '미기재', '수집URL': 'https://drug.hospitalk.net/item/202106398', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202106398', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201803837', 'ITEM_NAME': '경방향사평위산연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초연조엑스(2.1~2.5→1);목향연조엑스(2.0~2.5→1);사인연조엑스(3.1∼3.8→1);후박연조엑스(5.4∼7.4→1);곽향연조엑스(2.8~3.4→1);지실연조엑스(3.6~4.4→1);향부자연조엑스(2.8~3.5→1);진피연조엑스(2.3~2.8→1);생강연조엑스(5.1~6.9→1);창출연조엑스(2.9~3.6→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2020-08-21', 'BAR_CODE': '8806613049908,8806613049915,8806613049922', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268186]감초연조엑스(2.1~2.5→1)|[M268321]목향연조엑스(2.0~2.5→1)|[M268069]사인연조엑스(3.1∼3.8→1)|[M268058]후박연조엑스(5.4∼7.4→1)|[M268320]곽향연조엑스(2.8~3.4→1)|[M266607]지실연조엑스(3.6~4.4→1)|[M268319]향부자연조엑스(2.8~3.5→1)|[M266591]진피연조엑스(2.3~2.8→1)|[M268065]생강연조엑스(5.1~6.9→1)|[M266600]창출연조엑스(2.9~3.6→1)', '함량_원료성분원문': '총량 : 1회 용량(10 g/포) 중|성분명 : 창출연조엑스(2.9~3.6→1)|분량 : 775.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 생강연조엑스(5.1~6.9→1)|분량 : 85.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 진피연조엑스(2.3~2.8→1)|분량 : 500.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 향부자연조엑스(2.8~3.5→1)|분량 : 400.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 지실연조엑스(3.6~4.4→1)|분량 : 250.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 곽향연조엑스(2.8~3.4→1)|분량 : 330.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 후박연조엑스(5.4∼7.4→1)|분량 : 140.8|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 사인연조엑스(3.1∼3.8→1)|분량 : 255.2|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 목향연조엑스(2.0~2.5→1)|분량 : 283.5|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10 g/포) 중|성분명 : 감초연조엑스(2.1~2.5→1)|분량 : 277.2|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회 용량(10 g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/201803837', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201803837', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005710', 'ITEM_NAME': '경방향성파적환엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대황;박하;아선약;가자;천궁;사인;감초;길경;연교', 'ENTP_NAME': '경방신약(주)', 'CHART': '담갈색의 과립제', 'CHANGE_DATE': '2019-09-20', 'BAR_CODE': '8806613020303,8806613020310,8806613020327,8806613020334,8806613020341', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040073]대황|[M040198]박하|[M040350]아선약|[M050005]가자|[M040550]천궁|[M095260]사인|[M040006]감초|[M040048]길경|[M051105]연교', '함량_원료성분원문': '총량 : 1회 용량(2.5그램) 중|성분명 : 연교|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램) 중|성분명 : 길경|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램) 중|성분명 : 감초|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램) 중|성분명 : 사인|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램) 중|성분명 : 천궁|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램) 중|성분명 : 가자|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램) 중|성분명 : 아선약|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램) 중|성분명 : 박하|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램) 중|성분명 : 대황|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1회 용량(2.5그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005710', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005710', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201706373', 'ITEM_NAME': '경방형개연교탕연조엑스(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '백지연조엑스(3.6~4.4→1);황금연조엑스(1.5~1.9→1);지각 연조엑스(1.5~1.8→1);시호연조엑스(3.6~4.4→1);천궁연조엑스(2.1~2.6→1);당귀연조엑스(2.8~3.4→1);방풍연조엑스(2.5~3.1→1);연교연조엑스(3.6~4.4→1);형개 연조엑스(4.3~5.9→1);길경 연조엑스(2.3~2.8→1);작약 연조엑스(2.8~3.4→1);치자연조엑스(2.1~2.6→1);감초 연조엑스(2.1∼2.5→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 연조엑스가 충전된 알루미늄포', 'CHANGE_DATE': '2023-07-07', 'BAR_CODE': '8806613048109,8806613048116,8806613048123,8806613048130', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M266599]백지연조엑스(3.6~4.4→1)|[M266601]황금연조엑스(1.5~1.9→1)|[M117331]지각 연조엑스(1.5~1.8→1)|[M266614]시호연조엑스(3.6~4.4→1)|[M279375]천궁연조엑스(2.1~2.6→1)|[M279374]당귀연조엑스(2.8~3.4→1)|[M266597]방풍연조엑스(2.5~3.1→1)|[M266612]연교연조엑스(3.6~4.4→1)|[M275846]형개 연조엑스(4.3~5.9→1)|[M116712]길경 연조엑스(2.3~2.8→1)|[M117955]작약 연조엑스(2.8~3.4→1)|[M269893]치자연조엑스(2.1~2.6→1)|[M272009]감초 연조엑스(2.1∼2.5→1)', '함량_원료성분원문': '총량 : 1회 용량(10g/포) 중|성분명 : 형개 연조엑스(4.3~5.9→1)|분량 : 176.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 길경 연조엑스(2.3~2.8→1)|분량 : 343.2|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 작약 연조엑스(2.8~3.4→1)|분량 : 290.4|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 치자연조엑스(2.1~2.6→1)|분량 : 378.4|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 감초 연조엑스(2.1∼2.5→1)|분량 : 277.2|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 연교연조엑스(3.6~4.4→1)|분량 : 220.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 방풍연조엑스(2.5~3.1→1)|분량 : 316.8|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 당귀연조엑스(2.8~3.4→1)|분량 : 290.4|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 천궁연조엑스(2.1~2.6→1)|분량 : 378.4|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 시호연조엑스(3.6~4.4→1)|분량 : 220.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 지각 연조엑스(1.5~1.8→1)|분량 : 545.6|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 황금연조엑스(1.5~1.9→1)|분량 : 519.2|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1회 용량(10g/포) 중|성분명 : 백지연조엑스(3.6~4.4→1)|분량 : 220.0|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회 용량(10g/포) 중', '수집URL': 'https://drug.hospitalk.net/item/201706373', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201706373', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005645', 'ITEM_NAME': '경방황련해독탕산(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '치자엑스산;황백엑스산;황금엑스산;황련엑스산', 'ENTP_NAME': '경방신약(주)', 'CHART': '갈색의 가루', 'CHANGE_DATE': '2023-02-13', 'BAR_CODE': '8806613021607,8806613021614,8806613021621,8806613021638,8806613021645,8806613021652,8806613021669,8806613045702,8806613045719,8806613045726,8806613045733,8806613045740,8806613045757', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089503]치자엑스산|[M085093]황백엑스산|[M089535]황금엑스산|[M089522]황련엑스산', '함량_원료성분원문': '총량 : 1회 용량(1.88그램) 중|성분명 : 황련엑스산|분량 : 0.28|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(1.88그램) 중|성분명 : 황금엑스산|분량 : 0.70|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(1.88그램) 중|성분명 : 황백엑스산|분량 : 0.35|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(1.88그램) 중|성분명 : 치자엑스산|분량 : 0.55|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '1회 용량(1.88그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200005645', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005645', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201904565', 'ITEM_NAME': '경방황련해독탕정(단미엑스혼합제)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '치자연조엑스(2.1~2.6→1);황금연조엑스(1.5~1.9→1);황련연조엑스(4.1~5.6→1);황백연조엑스(1.9~2.3→1)', 'ENTP_NAME': '경방신약(주)', 'CHART': '적갈색의 장방형 필름코팅정제', 'CHANGE_DATE': '2025-03-27', 'BAR_CODE': '8806613051802,8806613051819,8806613051826', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M269893]치자연조엑스(2.1~2.6→1)|[M117845]황금연조엑스(1.5~1.9→1)|[M269894]황련연조엑스(4.1~5.6→1)|[M268981]황백연조엑스(1.9~2.3→1)', '함량_원료성분원문': '총량 : 1회1,770밀리그램|성분명 : 치자연조엑스(2.1~2.6→1)|분량 : 670.8|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회1,770밀리그램|성분명 : 황금연조엑스(1.5~1.9→1)|분량 : 920.4|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회1,770밀리그램|성분명 : 황련연조엑스(4.1~5.6→1)|분량 : 327.6|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1회1,770밀리그램|성분명 : 황백연조엑스(1.9~2.3→1)|분량 : 764.4|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '11,770', '수집URL': 'https://drug.hospitalk.net/item/201904565', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201904565', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199602918', 'ITEM_NAME': '경신환', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '우슬;골쇄보;당귀;황백;창출;작약;황기;오미자;인삼;강활;귀판;숙지황;백출;방기;산약;방풍;두충;보골지;구기자;토사자', 'ENTP_NAME': '경진제약(주)', 'CHART': '흑갈색의 환제', 'CHANGE_DATE': '2014-03-27', 'BAR_CODE': '8806604000109,8806604000116,8806604000123,8806604000130,8806604000147,8806604000154,8806604000161', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040476]우슬|[M086023]골쇄보|[M040070]당귀|[M040793]황백|[M040548]창출|[M040523]작약|[M040790]황기|[M040445]오미자|[M051291]인삼|[M050022]강활|[M083081]귀판|[M051364]숙지황|[M040214]백출|[M050533]방기|[M040258]산약|[M040205]방풍|[M040089]두충|[M050609]보골지|[M040030]구기자|[M050719]토사자', '함량_원료성분원문': '총량 : 1포(160밀리그람×20환)중|성분명 : 숙지황|분량 : 150|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 백출|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 방기|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 산약|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 방풍|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 두충|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 보골지|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 구기자|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 토사자|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 귀판|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 강활|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 우슬|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 골쇄보|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 당귀|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : 데쿠르신으로서 5.9밀리그람;총량 : 1포(160밀리그람×20환)중|성분명 : 황백|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : 베르베린으로서 0.6밀리그람;총량 : 1포(160밀리그람×20환)중|성분명 : 창출|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 작약|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : 패오니플로린으로서 2.85 밀리그람;총량 : 1포(160밀리그람×20환)중|성분명 : 황기|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160밀리그람×20환)중|성분명 : 오미자|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : 슈잔드린으로서 0.4 밀리그람;총량 : 1포(160밀리그람×20환)중|성분명 : 인삼|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : 진세노사이드Rb1으로서 0.2 밀리그람', '함량_총량기준': '1포(160밀리그람×20환)중', '수집URL': 'https://drug.hospitalk.net/item/199602918', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199602918', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199803342', 'ITEM_NAME': '경진 반하후박탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '수침건조엑스;반하;복령;후박;자소엽;생강', 'ENTP_NAME': '경진제약(주)', 'CHART': '담갈색의 과립제', 'CHANGE_DATE': '2010-03-09', 'BAR_CODE': '8806604000307,8806604000314,8806604000321,8806604000338,8806604000345,8806604000352', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M086656]수침건조엑스|[M040202]반하|[M040225]복령|[M040813]후박|[M051301]자소엽|[M050752]생강', '함량_원료성분원문': '총량 : 1포(3.0g) 중|성분명 : 생강|분량 : 1.33|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 자소엽|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 후박|분량 : 1.0|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 복령|분량 : 1.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 반하|분량 : 2.0|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 수침건조엑스|분량 : 500|단위 : 밀리그램|규격 : .|성분정보 :', '함량_총량기준': '1포(3.0g) 중', '수집URL': 'https://drug.hospitalk.net/item/199803342', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199803342', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200704248', 'ITEM_NAME': '경진 인삼패독산엑스 과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '길경;지각;독활;전호;시호;감초;강활;천궁;복령;인삼', 'ENTP_NAME': '경진제약(주)', 'CHART': '황갈색의 과립제', 'CHANGE_DATE': '2010-04-09', 'BAR_CODE': '8806604000901,8806604000918,8806604000925,8806604000932,8806604000949,8806604000956,8806604000963,8806604000970,8806604000987', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040048]길경|[M051351]지각|[M050227]독활|[M051318]전호|[M040336]시호|[M040006]감초|[M050022]강활|[M040550]천궁|[M040225]복령|[M051291]인삼', '함량_원료성분원문': '총량 : 전과 동일(1포 3.0그램 중)|성분명 : 인삼|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 전과 동일(1포 3.0그램 중)|성분명 : 복령|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 전과 동일(1포 3.0그램 중)|성분명 : 천궁|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 전과 동일(1포 3.0그램 중)|성분명 : 강활|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 전과 동일(1포 3.0그램 중)|성분명 : 감초|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 전과 동일(1포 3.0그램 중)|성분명 : 시호|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 전과 동일(1포 3.0그램 중)|성분명 : 전호|분량 : 1.25|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 전과 동일(1포 3.0그램 중)|성분명 : 독활|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 전과 동일(1포 3.0그램 중)|성분명 : 지각|분량 : 1.25|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 전과 동일(1포 3.0그램 중)|성분명 : 길경|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '전과 동일(1포 3.0그램 중)', '수집URL': 'https://drug.hospitalk.net/item/200704248', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200704248', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199803254', 'ITEM_NAME': '경진당귀수산엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '당귀;도인;향부자;홍화;오약;소목;계심;작약;감초', 'ENTP_NAME': '경진제약(주)', 'CHART': '담황색의 과립제.', 'CHANGE_DATE': '2014-04-11', 'BAR_CODE': '8806604002509,8806604002516,8806604002523,8806604002530,8806604002547,8806604002554,8806604002561,8806604002578', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040070]당귀|[M040086]도인|[M040228]향부자|[M040785]홍화|[M051153]오약|[M080844]소목|[M050023]계심|[M040523]작약|[M040006]감초', '함량_원료성분원문': '총량 : 1포(3.0g) 중|성분명 : 감초|분량 : 0.63|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 작약|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 계심|분량 : 0.75|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 소목|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 오약|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 홍화|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 향부자|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 도인|분량 : 0.88|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 당귀|분량 : 1.88|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1포(3.0g) 중', '수집URL': 'https://drug.hospitalk.net/item/199803254', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199803254', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202106998', 'ITEM_NAME': '경진방풍통성산정(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '생강;작약;천궁;연교;박하;방풍;마황;대황;활석;감초;당귀;망초;길경;황금;석고;치자;형개;백출', 'ENTP_NAME': '경진제약(주)', 'CHART': '황색의 원형 필름코팅정제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '미기재', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050752]생강|[M040523]작약|[M040550]천궁|[M051105]연교|[M040198]박하|[M040205]방풍|[M040135]마황|[M040073]대황|[M279368]활석|[M040006]감초|[M040070]당귀|[M088654]망초|[M040048]길경|[M040789]황금|[M040279]석고|[M040564]치자|[M051936]형개|[M040214]백출', '함량_원료성분원문': '총량 : 1정470밀리그램|성분명 : 당귀|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정470밀리그램|성분명 : 망초|분량 : 166.7|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1정470밀리그램|성분명 : 길경|분량 : 223.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정470밀리그램|성분명 : 황금|분량 : 223.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정470밀리그램|성분명 : 석고|분량 : 333.3|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1정470밀리그램|성분명 : 치자|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정470밀리그램|성분명 : 형개|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정470밀리그램|성분명 : 백출|분량 : 223.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정470밀리그램|성분명 : 감초|분량 : 223.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정470밀리그램|성분명 : 활석|분량 : 556.7|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1정470밀리그램|성분명 : 생강|분량 : 133.3|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1정470밀리그램|성분명 : 작약|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정470밀리그램|성분명 : 천궁|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정470밀리그램|성분명 : 연교|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정470밀리그램|성분명 : 박하|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정470밀리그램|성분명 : 방풍|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정470밀리그램|성분명 : 마황|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정470밀리그램|성분명 : 대황|분량 : 166.7|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1470', '수집URL': 'https://drug.hospitalk.net/item/202106998', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202106998', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200202804', 'ITEM_NAME': '경진변방우황청심원(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '용뇌;영양각;건강;백렴;인삼;포황;신곡;육계;대두황권;아교;작약;사향;우황;감초;산약;맥문동;당귀;방풍;백출;황금;시호;길경;행인;복령;천궁', 'ENTP_NAME': '경진제약(주)', 'CHART': '금박을 입힌 환제', 'CHANGE_DATE': '2019-02-15', 'BAR_CODE': '8806604003605,8806604003612,8806604003629,8806604003636,8806604003643', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051197]용뇌|[M051133]영양각|[M040007]건강|[M050541]백렴|[M040213]인삼|[M051762]포황|[M050891]신곡|[M050036]육계|[M050191]대두황권|[M050905]아교|[M040523]작약|[M040253]사향|[M040478]우황|[M040006]감초|[M040258]산약|[M040139]맥문동|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040789]황금|[M040336]시호|[M040048]길경|[M040769]행인|[M040225]복령|[M040550]천궁', '함량_원료성분원문': '총량 : 1환(3.75g)중|성분명 : 산약|분량 : 282|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 맥문동|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 당귀|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 방풍|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 백출|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 황금|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 시호|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 길경|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 행인|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 복령|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 천궁|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 감초|분량 : 202|단위 : 밀리그램|규격 : KP|성분정보 : 글리시리진산으로서 4.0mg;총량 : 1환(3.75g)중|성분명 : 우황|분량 : 14|단위 : 밀리그램|규격 : KP|성분정보 : 결합형빌리루빈으로서 1.4mg;총량 : 1환(3.75g)중|성분명 : 사향|분량 : 5|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 용뇌|분량 : 41|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 영양각|분량 : 35|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 건강|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 백렴|분량 : 30|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 인삼|분량 : 97|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 포황|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 신곡|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 육계|분량 : 70|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 대두황권|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 아교|분량 : 70|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 작약|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1환(3.75g)중', '수집URL': 'https://drug.hospitalk.net/item/200202804', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200202804', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200612253', 'ITEM_NAME': '경진보화환', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '후박;향부자;연교;산사;신곡;반하;복령;진피;백출;내복자;지실;맥아;황금;황련', 'ENTP_NAME': '경진제약(주)', 'CHART': '흑갈색의 환제', 'CHANGE_DATE': '2009-03-31', 'BAR_CODE': '8806604004107,8806604004114,8806604004121,8806604004138,8806604004145,8806604004152,8806604004169,8806604004176', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040813]후박|[M040228]향부자|[M051105]연교|[M050729]산사|[M050891]신곡|[M040202]반하|[M040225]복령|[M040538]진피|[M040214]백출|[M210181]내복자|[M040536]지실|[M050407]맥아|[M040789]황금|[M040792]황련', '함량_원료성분원문': '총량 : 1포(160mg x 20환)중|성분명 : 백출|분량 : 366.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 내복자|분량 : 146.50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 지실|분량 : 73.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 맥아|분량 : 73.25|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 황금|분량 : 73.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 황련|분량 : 73.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 진피|분량 : 219.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 복령|분량 : 219.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 반하|분량 : 219.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 신곡|분량 : 219.75|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 산사|분량 : 219.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 연교|분량 : 146.50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 향부자|분량 : 146.50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 후박|분량 : 146.50|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1포(160mg x 20환)중', '수집URL': 'https://drug.hospitalk.net/item/200612253', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200612253', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200709745', 'ITEM_NAME': '경진사물탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '당귀;작약;천궁;숙지황', 'ENTP_NAME': '경진제약(주)', 'CHART': '갈색의 과립제', 'CHANGE_DATE': '2026-07-15', 'BAR_CODE': '8806604004503,8806604004510,8806604004527,8806604004534,8806604004541,8806604004558', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040070]당귀|[M040523]작약|[M040550]천궁|[M051364]숙지황', '함량_원료성분원문': '총량 : 1포(2.5그램)중|성분명 : 당귀|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(2.5그램)중|성분명 : 작약|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(2.5그램)중|성분명 : 천궁|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(2.5그램)중|성분명 : 숙지황|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1포(2.5그램)중', '수집URL': 'https://drug.hospitalk.net/item/200709745', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200709745', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199803251', 'ITEM_NAME': '경진소경활혈탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '용담;천궁;작약;지황;위령선;방기;생강;백지;감초;당귀;복령;강활;진피;우슬;백출;방풍;도인', 'ENTP_NAME': '경진제약(주)', 'CHART': '담갈색의 과립제', 'CHANGE_DATE': '2014-03-27', 'BAR_CODE': '8806604005005,8806604005012,8806604005029,8806604005036,8806604005043,8806604005050,8806604005067', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040474]용담|[M040550]천궁|[M040523]작약|[M040537]지황|[M083244]위령선|[M050533]방기|[M050752]생강|[M040216]백지|[M040006]감초|[M040070]당귀|[M040225]복령|[M050022]강활|[M040538]진피|[M040476]우슬|[M040214]백출|[M040205]방풍|[M040086]도인', '함량_원료성분원문': '총량 : 1포 중|성분명 : 복령|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 강활|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 진피|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 우슬|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 백출|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 방풍|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 도인|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 당귀|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 감초|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 백지|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 용담|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 천궁|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 작약|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 지황|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 위령선|분량 : 0.5|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포 중|성분명 : 방기|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 생강|분량 : 0.5|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '1포 중', '수집URL': 'https://drug.hospitalk.net/item/199803251', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199803251', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199803268', 'ITEM_NAME': '경진십미패독탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '복령;천궁;형개;생강;연교;앵피;독활;시호;길경;방풍;감초', 'ENTP_NAME': '경진제약(주)', 'CHART': '담갈색의 과립제', 'CHANGE_DATE': '2021-12-22', 'BAR_CODE': '8806604005708,8806604005715,8806604005722,8806604005739', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040225]복령|[M040550]천궁|[M051936]형개|[M050752]생강|[M051105]연교|[M051043]앵피|[M050227]독활|[M040336]시호|[M040048]길경|[M040205]방풍|[M040006]감초', '함량_원료성분원문': '총량 : 1포(3.0g) 중|성분명 : 감초|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 방풍|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 길경|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 시호|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 독활|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 앵피|분량 : 1|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 연교|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 생강|분량 : 1|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 형개|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 천궁|분량 : 1|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 복령|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1포(3.0g) 중', '수집URL': 'https://drug.hospitalk.net/item/199803268', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199803268', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200804799', 'ITEM_NAME': '경진쌍화탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '생강;작약;황기;대추;당귀;감초;육계;천궁;이상 건조엑스로서;숙지황', 'ENTP_NAME': '경진제약(주)', 'CHART': '암갈색의 과립제', 'CHANGE_DATE': '2010-03-09', 'BAR_CODE': '8806604013109,8806604013116,8806604013123,8806604013130,8806604013147,8806604013154', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050752]생강|[M040523]작약|[M040790]황기|[M040071]대추|[M040070]당귀|[M040006]감초|[M050036]육계|[M040550]천궁|[M219019]이상 건조엑스로서|[M051364]숙지황', '함량_원료성분원문': '총량 : 1포(3.0그람) 중|성분명 : 숙지황|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그람) 중|성분명 : 이상 건조엑스로서|분량 : 1350|단위 : 밀리그램|규격 : .|성분정보 : ;총량 : 1포(3.0그람) 중|성분명 : 천궁|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그람) 중|성분명 : 육계|분량 : 0.94|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그람) 중|성분명 : 감초|분량 : 0.94|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그람) 중|성분명 : 당귀|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그람) 중|성분명 : 대추|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그람) 중|성분명 : 황기|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그람) 중|성분명 : 작약|분량 : 3.13|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그람) 중|성분명 : 생강|분량 : 0.50|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '1포(3.0그람) 중', '수집URL': 'https://drug.hospitalk.net/item/200804799', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200804799', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201604522', 'ITEM_NAME': '경진안궁우황환(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '백출;작약;황련;백강잠;방풍;감초;꿀;사인;황금;호박;괄루근;우담남성;용뇌;우황;사향;전갈;반하', 'ENTP_NAME': '경진제약(주)', 'CHART': '금박을 환의환 갈색의 환제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '미기재', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040214]백출|[M040523]작약|[M040792]황련|[M050535]백강잠|[M040205]방풍|[M040006]감초|[M200168]꿀|[M095260]사인|[M040789]황금|[M051946]호박|[M095529]괄루근|[M051206]우담남성|[M051197]용뇌|[M040478]우황|[M040253]사향|[M051316]전갈|[M040202]반하', '함량_원료성분원문': '총량 : 1환(3.0g) 중|성분명 : 우담남성|분량 : 81.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 괄루근|분량 : 99.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 호박|분량 : 60.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 황금|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 사인|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 꿀|분량 : 1063.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 감초|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 백출|분량 : 30.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 작약|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 황련|분량 : 81.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 백강잠|분량 : 60.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 방풍|분량 : 81.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 용뇌|분량 : 13.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 우황|분량 : 26.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 사향|분량 : 6.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 전갈|분량 : 81.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.0g) 중|성분명 : 반하|분량 : 99.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1환(3.0g) 중', '수집URL': 'https://drug.hospitalk.net/item/201604522', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201604522', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200606462', 'ITEM_NAME': '경진양간환(보간환)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '숙지황;작약;천궁;방풍;강활;당귀', 'ENTP_NAME': '경진제약(주)', 'CHART': '흑갈색의 환제', 'CHANGE_DATE': '2010-03-09', 'BAR_CODE': '8806604005807,8806604005814,8806604005821,8806604005838,8806604005845,8806604005852,8806604005869,8806604005876', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051364]숙지황|[M040523]작약|[M040550]천궁|[M040205]방풍|[M050022]강활|[M040070]당귀', '함량_원료성분원문': '총량 : 1환(200mg)중|성분명 : 숙지황|분량 : 32.9|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(200mg)중|성분명 : 작약|분량 : 32.9|단위 : 밀리그램|규격 : KP|성분정보 : 페오니플로린으로서0.66밀리그람;총량 : 1환(200mg)중|성분명 : 천궁|분량 : 32.9|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(200mg)중|성분명 : 방풍|분량 : 28.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(200mg)중|성분명 : 강활|분량 : 28.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(200mg)중|성분명 : 당귀|분량 : 32.9|단위 : 밀리그램|규격 : KP|성분정보 : 데쿠르신으로서1.94밀리그람', '함량_총량기준': '1환(200mg)중', '수집URL': 'https://drug.hospitalk.net/item/200606462', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200606462', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201404211', 'ITEM_NAME': '경진억간산가진피반하엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '반하;진피;감초;시호;복령;백출;천궁;조구등;당귀', 'ENTP_NAME': '경진제약(주)', 'CHART': '담갈색 과립제', 'CHANGE_DATE': '2014-10-06', 'BAR_CODE': '8806604022101,8806604022118,8806604022125,8806604022132', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040202]반하|[M040538]진피|[M040006]감초|[M040336]시호|[M040225]복령|[M040214]백출|[M040550]천궁|[M051333]조구등|[M040070]당귀', '함량_원료성분원문': '총량 : 1회 용량(3그램) 중|성분명 : 당귀|분량 : 1.0|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3그램) 중|성분명 : 조구등|분량 : 1.0|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회 용량(3그램) 중|성분명 : 천궁|분량 : 1.0|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3그램) 중|성분명 : 백출|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3그램) 중|성분명 : 복령|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3그램) 중|성분명 : 시호|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3그램) 중|성분명 : 감초|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3그램) 중|성분명 : 진피|분량 : 1.0|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(3그램) 중|성분명 : 반하|분량 : 1.67|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1회 용량(3그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201404211', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201404211', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200606807', 'ITEM_NAME': '경진연령고본단', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '석창포;원지;택사;육종용;맥문동;생지황;숙지황;산약;우슬;두충;파극천;산초;천문동;토사자;구기자;산수유;복령;오미자;인삼;목향;백자인;복분자;차전자;지골피', 'ENTP_NAME': '경진제약(주)', 'CHART': '흑갈색의 환제', 'CHANGE_DATE': '2021-01-19', 'BAR_CODE': '8806604006002,8806604006019,8806604006026,8806604006033,8806604006040,8806604006057', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051377]석창포|[M040482]원지|[M040638]택사|[M051248]육종용|[M040139]맥문동|[M051363]생지황|[M051364]숙지황|[M040258]산약|[M040476]우슬|[M040089]두충|[M082557]파극천|[M040260]산초|[M051380]천문동|[M050719]토사자|[M040030]구기자|[M040257]산수유|[M040225]복령|[M040445]오미자|[M051291]인삼|[M040187]목향|[M050550]백자인|[M050621]복분자|[M040545]차전자|[M051352]지골피', '함량_원료성분원문': '총량 : 1환(190mg)중|성분명 : 토사자|분량 : 16|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(190mg)중|성분명 : 구기자|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 산수유|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 복령|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 오미자|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 인삼|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 목향|분량 : 8|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(190mg)중|성분명 : 백자인|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 복분자|분량 : 6|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 차전자|분량 : 6|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 지골피|분량 : 6|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 천문동|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 산초|분량 : 4|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 석창포|분량 : 4|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(190mg)중|성분명 : 원지|분량 : 4|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 택사|분량 : 4|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 육종용|분량 : 16|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(190mg)중|성분명 : 맥문동|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 생지황|분량 : 8|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(190mg)중|성분명 : 숙지황|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 산약|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 우슬|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 두충|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(190mg)중|성분명 : 파극천|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1환(190mg)중', '수집URL': 'https://drug.hospitalk.net/item/200606807', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200606807', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200810431', 'ITEM_NAME': '경진오약순기탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '백지;백강잠;지각;길경;건강;천궁;오약;진피;이상수침건조엑스;대추;생강;감초;마황', 'ENTP_NAME': '경진제약(주)', 'CHART': '담갈색의 과립제', 'CHANGE_DATE': '2009-04-30', 'BAR_CODE': '8806604014205,8806604014212,8806604014229,8806604014236,8806604014243,8806604014250', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040216]백지|[M050535]백강잠|[M051351]지각|[M040048]길경|[M040007]건강|[M040550]천궁|[M051153]오약|[M040538]진피|[M099148]이상수침건조엑스|[M040071]대추|[M050752]생강|[M040006]감초|[M040135]마황', '함량_원료성분원문': '총량 : 1회용량 (3.0g) 중|성분명 : 마황|분량 : 1.88|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 (3.0g) 중|성분명 : 감초|분량 : 0.38|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 (3.0g) 중|성분명 : 생강|분량 : 0.50|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회용량 (3.0g) 중|성분명 : 대추|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 (3.0g) 중|성분명 : 이상수침건조엑스|분량 : 1200|단위 : 밀리그램|규격 : .|성분정보 : ;총량 : 1회용량 (3.0g) 중|성분명 : 진피|분량 : 1.88|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 (3.0g) 중|성분명 : 오약|분량 : 1.88|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 (3.0g) 중|성분명 : 천궁|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 (3.0g) 중|성분명 : 백지|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 (3.0g) 중|성분명 : 백강잠|분량 : 1.25|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회용량 (3.0g) 중|성분명 : 지각|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 (3.0g) 중|성분명 : 길경|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량 (3.0g) 중|성분명 : 건강|분량 : 0.63|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1회용량 (3.0g) 중', '수집URL': 'https://drug.hospitalk.net/item/200810431', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200810431', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200810212', 'ITEM_NAME': '경진용담사간탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초;치자;용담;차전자;택사;황금;목통;지황;이상 건조엑스로서;당귀', 'ENTP_NAME': '경진제약(주)', 'CHART': '갈색의 과립제', 'CHANGE_DATE': '2010-03-09', 'BAR_CODE': '8806604013901,8806604013918,8806604013925,8806604013932,8806604013949,8806604013956,8806604013963', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040006]감초|[M040564]치자|[M040474]용담|[M040545]차전자|[M040638]택사|[M040789]황금|[M040186]목통|[M040537]지황|[M219019]이상 건조엑스로서|[M040070]당귀', '함량_원료성분원문': '총량 : 1포(3.0g)중|성분명 : 당귀|분량 : 1.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g)중|성분명 : 이상 건조엑스로서|분량 : 1.32|단위 : 그램|규격 : .|성분정보 : ;총량 : 1포(3.0g)중|성분명 : 지황|분량 : 1.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g)중|성분명 : 목통|분량 : 1.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g)중|성분명 : 황금|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g)중|성분명 : 택사|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g)중|성분명 : 차전자|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g)중|성분명 : 용담|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g)중|성분명 : 치자|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g)중|성분명 : 감초|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1포(3.0g)중', '수집URL': 'https://drug.hospitalk.net/item/200810212', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200810212', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199903467', 'ITEM_NAME': '경진우황청심원(사향대체물질엘-무스콘함유)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '백렴;건강;영양각;용뇌;감초;신곡;포황;인삼;육계;대두황권;아교;우황;행인;산약;L-무스콘;당귀;맥문동;방풍;백출;작약;황금;시호;길경;복령;천궁', 'ENTP_NAME': '경진제약(주)', 'CHART': '금박을 입힌 환제', 'CHANGE_DATE': '2019-02-22', 'BAR_CODE': '8806604006507,8806604006514,8806604006521', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050541]백렴|[M040007]건강|[M051133]영양각|[M051197]용뇌|[M040006]감초|[M050891]신곡|[M051762]포황|[M040213]인삼|[M050036]육계|[M050191]대두황권|[M050905]아교|[M040478]우황|[M040769]행인|[M040258]산약|[M213890]L-무스콘|[M040070]당귀|[M040139]맥문동|[M040205]방풍|[M040214]백출|[M040523]작약|[M040789]황금|[M040336]시호|[M040048]길경|[M040225]복령|[M040550]천궁', '함량_원료성분원문': '총량 : 1환(3.75g) 중|성분명 : L-무스콘|분량 : 75|단위 : 마이크로그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 당귀|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 맥문동|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 방풍|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 백출|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 작약|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 황금|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 시호|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 길경|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 복령|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 천궁|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 산약|분량 : 282|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 행인|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 우황|분량 : 14|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 용뇌|분량 : 41|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 영양각|분량 : 35|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 건강|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 백렴|분량 : 30|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 감초|분량 : 202|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 신곡|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 포황|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 인삼|분량 : 97|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 육계|분량 : 70|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 대두황권|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 아교|분량 : 70|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1환(3.75g) 중', '수집URL': 'https://drug.hospitalk.net/item/199903467', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199903467', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199903466', 'ITEM_NAME': '경진원방우황청심원(사향대체물질엘-무스콘함유)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '영양각;용뇌;건강;백렴;감초;인삼;포황;신곡;육계;대두황권;아교;우황;행인;산약;L-무스콘;당귀;맥문동;방풍;백출;작약;황금;길경;복령;시호;천궁', 'ENTP_NAME': '경진제약(주)', 'CHART': '금박을 입힌 환제', 'CHANGE_DATE': '2024-04-11', 'BAR_CODE': '8806604006705,8806604006712', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051133]영양각|[M051197]용뇌|[M040007]건강|[M050541]백렴|[M040006]감초|[M040213]인삼|[M051762]포황|[M050891]신곡|[M050036]육계|[M050191]대두황권|[M050905]아교|[M040478]우황|[M040769]행인|[M040258]산약|[M213890]L-무스콘|[M040070]당귀|[M040139]맥문동|[M040205]방풍|[M040214]백출|[M040523]작약|[M040789]황금|[M040048]길경|[M040225]복령|[M040336]시호|[M040550]천궁', '함량_원료성분원문': '총량 : 1환(3.75g) 중|성분명 : L-무스콘|분량 : 570|단위 : 마이크로그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 당귀|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 맥문동|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 방풍|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 백출|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 작약|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 황금|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 길경|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 복령|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 시호|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 천궁|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 산약|분량 : 263|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 행인|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 우황|분량 : 45|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 영양각|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 용뇌|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 건강|분량 : 28|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 백렴|분량 : 28|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 감초|분량 : 188|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 인삼|분량 : 94|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 포황|분량 : 94|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 신곡|분량 : 94|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 육계|분량 : 66|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 대두황권|분량 : 66|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 아교|분량 : 66|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1환(3.75g) 중', '수집URL': 'https://drug.hospitalk.net/item/199903466', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199903466', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199703159', 'ITEM_NAME': '경진원방우황청심원(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '용뇌;영양각;건강;백렴;인삼;포황;신곡;육계;대두황권;아교;작약;사향;우황;감초;산약;맥문동;당귀;방풍;백출;황금;시호;길경;행인;복령;천궁', 'ENTP_NAME': '경진제약(주)', 'CHART': '금박을 입힌 환제', 'CHANGE_DATE': '2019-02-22', 'BAR_CODE': '8806604006606,8806604006613,8806604006620,8806604006637', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051197]용뇌|[M051133]영양각|[M040007]건강|[M050541]백렴|[M040213]인삼|[M051762]포황|[M050891]신곡|[M050036]육계|[M050191]대두황권|[M050905]아교|[M040523]작약|[M040253]사향|[M040478]우황|[M040006]감초|[M040258]산약|[M040139]맥문동|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040789]황금|[M040336]시호|[M040048]길경|[M040769]행인|[M040225]복령|[M040550]천궁', '함량_원료성분원문': '총량 : 1환(3.75g)중|성분명 : 산약|분량 : 263|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 맥문동|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 당귀|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 방풍|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 백출|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 황금|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 시호|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 길경|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 행인|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 복령|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 천궁|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 감초|분량 : 188|단위 : 밀리그램|규격 : KP|성분정보 : 글리시리진산으로서 3.8mg;총량 : 1환(3.75g)중|성분명 : 우황|분량 : 45|단위 : 밀리그램|규격 : KP|성분정보 : 결합형빌리루빈으로서 4.5mg;총량 : 1환(3.75g)중|성분명 : 사향|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 용뇌|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 영양각|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 건강|분량 : 28|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 백렴|분량 : 28|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 인삼|분량 : 94|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 포황|분량 : 94|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 신곡|분량 : 94|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 육계|분량 : 66|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 대두황권|분량 : 66|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 아교|분량 : 66|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 작약|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1환(3.75g)중', '수집URL': 'https://drug.hospitalk.net/item/199703159', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199703159', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200801127', 'ITEM_NAME': '경진원방우황청심원액(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건강;용뇌;영양각;사향;대두황권;아교;작약;황금;방풍;백출;맥문동;백렴;신곡;계피;감초;당귀;길경;복령;시호;행인;천궁;우황;산약;인삼;포황', 'ENTP_NAME': '경진제약(주)', 'CHART': '생약의 독특한 맛과 향취가 있는 갈색의 액제', 'CHANGE_DATE': '2019-02-22', 'BAR_CODE': '8806775006306', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040007]건강|[M051197]용뇌|[M051133]영양각|[M040253]사향|[M050191]대두황권|[M050905]아교|[M040523]작약|[M040789]황금|[M040205]방풍|[M040214]백출|[M040139]맥문동|[M050541]백렴|[M050891]신곡|[M040016]계피|[M040006]감초|[M040070]당귀|[M040048]길경|[M040225]복령|[M040336]시호|[M040769]행인|[M040550]천궁|[M040478]우황|[M040258]산약|[M051291]인삼|[M090765]포황', '함량_원료성분원문': '총량 : 1병(50mL) 중|성분명 : 감초|분량 : 188|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 당귀|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 길경|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 복령|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 시호|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 행인|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 천궁|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 우황|분량 : 45|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 산약|분량 : 263|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 인삼|분량 : 94|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 포황|분량 : 94|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 계피|분량 : 66|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 신곡|분량 : 94|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 백렴|분량 : 28|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 건강|분량 : 28|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 용뇌|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 영양각|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 사향|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 대두황권|분량 : 66|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 아교|분량 : 66|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 작약|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 황금|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 방풍|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 백출|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(50mL) 중|성분명 : 맥문동|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1병(50mL) 중', '수집URL': 'https://drug.hospitalk.net/item/200801127', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200801127', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200700037', 'ITEM_NAME': '경진유락과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '차전자피;센나열매', 'ENTP_NAME': '경진제약(주)', 'CHART': '갈색의 과립제', 'CHANGE_DATE': '2025-04-14', 'BAR_CODE': '8806604006804,8806604006811,8806604006828,8806604006835,8806604006842,8806604006859,8806604006866', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081198]차전자피|[M050805]센나열매', '함량_원료성분원문': '총량 : 1포 (3.5g) 중|성분명 : 차전자피|분량 : 2,168|단위 : 밀리그램|규격 : BP|성분정보 : ;총량 : 1포 (3.5g) 중|성분명 : 센나열매|분량 : 496|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '1포 (3.5g) 중', '수집URL': 'https://drug.hospitalk.net/item/200700037', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200700037', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198701801', 'ITEM_NAME': '경진육미지황환', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '택사;복령;목단피;산수유;산약;숙지황', 'ENTP_NAME': '경진제약(주)', 'CHART': '황갈색의 환제이다.', 'CHANGE_DATE': '2010-03-09', 'BAR_CODE': '8806604006903,8806604006910,8806604006927,8806604006934,8806604006941', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040638]택사|[M040225]복령|[M040185]목단피|[M040257]산수유|[M040258]산약|[M051364]숙지황', '함량_원료성분원문': '총량 : 1포(4그램)중|성분명 : 숙지황|분량 : 640|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(4그램)중|성분명 : 산약|분량 : 320|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(4그램)중|성분명 : 산수유|분량 : 320|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(4그램)중|성분명 : 목단피|분량 : 240|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(4그램)중|성분명 : 복령|분량 : 240|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(4그램)중|성분명 : 택사|분량 : 240|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1포(4그램)중', '수집URL': 'https://drug.hospitalk.net/item/198701801', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198701801', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199803257', 'ITEM_NAME': '경진작약감초탕엑스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초;작약', 'ENTP_NAME': '경진제약(주)', 'CHART': '담갈색의 과립제', 'CHANGE_DATE': '2010-04-09', 'BAR_CODE': '8806604007702,8806604007719,8806604007726,8806604007733,8806604007740,8806604007757', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040006]감초|[M040523]작약', '함량_원료성분원문': '총량 : 1포 중|성분명 : 작약|분량 : 2|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포 중|성분명 : 감초|분량 : 2|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1포 중', '수집URL': 'https://drug.hospitalk.net/item/199803257', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199803257', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200606571', 'ITEM_NAME': '경진천왕보심단', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '생지황;천문동;맥문동;당귀;원지;현삼;백자인;단삼;황련;길경;복령;인삼;산조인;오미자', 'ENTP_NAME': '경진제약(주)', 'CHART': '흑갈색의 환제', 'CHANGE_DATE': '2009-04-30', 'BAR_CODE': '8806604007900,8806604007917,8806604007924,8806604007931,8806604007948,8806604007955,8806604007962,8806604007979,8806604007986,8806604007993,8806604024310', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051363]생지황|[M051380]천문동|[M040139]맥문동|[M040070]당귀|[M040482]원지|[M051932]현삼|[M050550]백자인|[M050176]단삼|[M040792]황련|[M040048]길경|[M040225]복령|[M051291]인삼|[M225911]산조인|[M040445]오미자', '함량_원료성분원문': '총량 : 1포(160mg x 20환)중|성분명 : 황련|분량 : 250.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 길경|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 복령|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 인삼|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 산조인|분량 : 125.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 오미자|분량 : 125.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 단삼|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 백자인|분량 : 125.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 생지황|분량 : 500.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 천문동|분량 : 125.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 맥문동|분량 : 125.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 당귀|분량 : 125.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 원지|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(160mg x 20환)중|성분명 : 현삼|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1포(160mg x 20환)중', '수집URL': 'https://drug.hospitalk.net/item/200606571', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200606571', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198701810', 'ITEM_NAME': '경진팔미환', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '정제부자;육계;목단피;복령;택사;산약;산수유;숙지황', 'ENTP_NAME': '경진제약(주)', 'CHART': '흑갈색의 환제이다', 'CHANGE_DATE': '2010-03-09', 'BAR_CODE': '8806604008402,8806604008419,8806604008426,8806604008433,8806604008440', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M201585]정제부자|[M050036]육계|[M040185]목단피|[M040225]복령|[M040638]택사|[M040258]산약|[M040257]산수유|[M051364]숙지황', '함량_원료성분원문': '총량 : 1포(3.2그램)중|성분명 : 숙지황|분량 : 593|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.2그램)중|성분명 : 산수유|분량 : 296|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.2그램)중|성분명 : 산약|분량 : 296|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.2그램)중|성분명 : 택사|분량 : 222|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.2그램)중|성분명 : 복령|분량 : 222|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.2그램)중|성분명 : 목단피|분량 : 222|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.2그램)중|성분명 : 육계|분량 : 74|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.2그램)중|성분명 : 정제부자|분량 : 74|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1포(3.2그램)중', '수집URL': 'https://drug.hospitalk.net/item/198701810', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198701810', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200103239', 'ITEM_NAME': '경진헤파신캡슐(배농산급탕)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '감초;대추;건강;길경;작약;지실', 'ENTP_NAME': '경진제약(주)', 'CHART': '황갈색의 분말이 충전된 상부 연청색, 하부 살구색의 캡슐', 'CHANGE_DATE': '2025-03-10', 'BAR_CODE': '8806604008808,8806604008815,8806604008822,8806604008839', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040006]감초|[M040071]대추|[M040007]건강|[M040048]길경|[M040523]작약|[M040536]지실', '함량_원료성분원문': '총량 : 1캡슐(550밀리그램) 중|성분명 : 지실|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1캡슐(550밀리그램) 중|성분명 : 작약|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : 패오니플로린으로서 10.0밀리그램;총량 : 1캡슐(550밀리그램) 중|성분명 : 길경|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1캡슐(550밀리그램) 중|성분명 : 건강|분량 : 0.17|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1캡슐(550밀리그램) 중|성분명 : 대추|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1캡슐(550밀리그램) 중|성분명 : 감초|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : 글리시리진산으로서 10.0밀리그램', '함량_총량기준': '1캡슐(550밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200103239', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200103239', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200713453', 'ITEM_NAME': '경통환(소경활혈탕)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '방풍;백지;강활;복령;우슬;도인;천궁;진피;이상 건조엑스로서;작약;위령선;감초;용담;방기;백출;당귀;지황;생강', 'ENTP_NAME': '(주)아이월드제약', 'CHART': '흑색의 환제', 'CHANGE_DATE': '2014-11-26', 'BAR_CODE': '8806696029408,8806696029415,8806696029422,8806696029439', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040205]방풍|[M040216]백지|[M050022]강활|[M040225]복령|[M040476]우슬|[M040086]도인|[M040550]천궁|[M040538]진피|[M219019]이상 건조엑스로서|[M040523]작약|[M083244]위령선|[M040006]감초|[M040474]용담|[M050533]방기|[M040214]백출|[M040070]당귀|[M040537]지황|[M050752]생강', '함량_원료성분원문': '총량 : 1회용량(2.6g,20환)중|성분명 : 위령선|분량 : 0.50|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 감초|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 용담|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 방기|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 백출|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 당귀|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 지황|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 생강|분량 : 0.50|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 작약|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 이상 건조엑스로서|분량 : 1.35|단위 : 그램|규격 : .|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 방풍|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 백지|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 강활|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 복령|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 우슬|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 도인|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 천궁|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.6g,20환)중|성분명 : 진피|분량 : 0.50|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1회용량(2.6g,20환)중', '수집URL': 'https://drug.hospitalk.net/item/200713453', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200713453', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005855', 'ITEM_NAME': '경혈환(계지복령환)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '작약;도인;목단피;복령;계지', 'ENTP_NAME': '경방신약(주)', 'CHART': '회갈색의 환제', 'CHANGE_DATE': '2020-05-26', 'BAR_CODE': '8806613022000,8806613022017,8806613022024,8806613022031,8806613022048,8806613022055', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040523]작약|[M040086]도인|[M040185]목단피|[M040225]복령|[M050037]계지', '함량_원료성분원문': '총량 : 1회3.2그램|성분명 : 계지|분량 : 500|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1회3.2그램|성분명 : 복령|분량 : 500|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.2그램|성분명 : 목단피|분량 : 500|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.2그램|성분명 : 도인|분량 : 500|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회3.2그램|성분명 : 작약|분량 : 500|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '13.2', '수집URL': 'https://drug.hospitalk.net/item/200005855', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005855', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198300045', 'ITEM_NAME': '계령과립(계지복령환)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '계지복령환 연조엑스', 'ENTP_NAME': '(주)한풍제약', 'CHART': '담갈색의 과립제', 'CHANGE_DATE': '2026-01-22', 'BAR_CODE': '8806581001106,8806581001113,8806581001120,8806581001137,8806581077408,8806581077415', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M111097]계지복령환 연조엑스', '함량_원료성분원문': '총량 : 1회4그램|성분명 : 계지복령환 연조엑스|분량 : 1330|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '14', '수집URL': 'https://drug.hospitalk.net/item/198300045', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198300045', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '197700011', 'ITEM_NAME': '계령대과립(계지복령환료가대황엑스과립)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '계지복령환료가대황연조엑스', 'ENTP_NAME': '(주)한풍제약', 'CHART': '담갈색의  과립제.', 'CHANGE_DATE': '2026-01-22', 'BAR_CODE': '8806581001205,8806581001212,8806581001229', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268955]계지복령환료가대황연조엑스', '함량_원료성분원문': '총량 : 1회4그램|성분명 : 계지복령환료가대황연조엑스|분량 : 1200|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '14', '수집URL': 'https://drug.hospitalk.net/item/197700011', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=197700011', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201801425', 'ITEM_NAME': '계안겔(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '디펜히드라민;디부카인염산염;크로타미톤;L-멘톨;dl-캄파;에녹솔론', 'ENTP_NAME': '동아제약(주)', 'CHART': '이 약은 무색 ~ 미황색의 투명한 겔제이다.', 'CHANGE_DATE': '2022-08-31', 'BAR_CODE': '8806265011803,8806265011810', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040108]디펜히드라민|[M222965]디부카인염산염|[M051499]크로타미톤|[M279284]L-멘톨|[M204423]dl-캄파|[M215133]에녹솔론', '함량_원료성분원문': '총량 : 1g 중|성분명 : 디펜히드라민|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1g 중|성분명 : 디부카인염산염|분량 : 5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1g 중|성분명 : 크로타미톤|분량 : 50|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1g 중|성분명 : L-멘톨|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1g 중|성분명 : dl-캄파|분량 : 29.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1g 중|성분명 : 에녹솔론|분량 : 1|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '1g 중', '수집URL': 'https://drug.hospitalk.net/item/201801425', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201801425', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200202997', 'ITEM_NAME': '고닐고포르테경고제', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '살리실산;락트산', 'ENTP_NAME': '유니메드제약(주)', 'CHART': '황갈색의 반창고 가운데에 원형의 스폰지로 둘러싸인 유황색의 약고가 있는 경고제', 'CHANGE_DATE': '2025-08-29', 'BAR_CODE': '8806495001001,8806495001018', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040264]살리실산|[M223371]락트산', '함량_원료성분원문': '총량 : 1매(약고120밀리그램, 약면 78.5제곱밀리미터 : 직경 10밀리미터)|성분명 : 살리실산|분량 : 20.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1매(약고120밀리그램, 약면 78.5제곱밀리미터 : 직경 10밀리미터)|성분명 : 락트산|분량 : 4.2|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1매(약고120밀리그램, 약면 78.5제곱밀리미터 : 직경 10밀리미터)', '수집URL': 'https://drug.hospitalk.net/item/200202997', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200202997', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '197500291', 'ITEM_NAME': '고려됴고약', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '연단;대황;백렴;황납;작약;황백;백지;황기;목별자;몰약;유향;등피;황;황금;행인;당귀;백급;육계;현삼;생지황', 'ENTP_NAME': '천우신약(주)', 'CHART': '흑갈색의 경고제(고약) 담황갈색내지 황갈색의 경고제(발근고)', 'CHANGE_DATE': '2008-02-02', 'BAR_CODE': '8806638000908,8806638000915,8806638000922', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051106]연단|[M040073]대황|[M050541]백렴|[M040791]황납|[M040523]작약|[M040793]황백|[M040216]백지|[M040790]황기|[M050499]목별자|[M040188]몰약|[M051238]유향|[M040090]등피|[M040787]황|[M040789]황금|[M040769]행인|[M040070]당귀|[M050538]백급|[M050036]육계|[M051932]현삼|[M051363]생지황', '함량_원료성분원문': '총량 : 10그람중|성분명 : 등피|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 10그람중|성분명 : 황|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램 중|성분명 : 황금|분량 : 75.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램 중|성분명 : 행인|분량 : 18.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램 중|성분명 : 당귀|분량 : 18.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램 중|성분명 : 백급|분량 : 18.75|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1그램 중|성분명 : 육계|분량 : 18.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램 중|성분명 : 현삼|분량 : 18.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램 중|성분명 : 생지황|분량 : 18.75|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1그램 중|성분명 : 유향|분량 : 18.75|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1그램 중|성분명 : 몰약|분량 : 18.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램 중|성분명 : 연단|분량 : 250.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1그램 중|성분명 : 대황|분량 : 75.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램 중|성분명 : 백렴|분량 : 37.5|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1그램 중|성분명 : 황납|분량 : 37.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램 중|성분명 : 작약|분량 : 18.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램 중|성분명 : 황백|분량 : 18.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램 중|성분명 : 백지|분량 : 18.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램 중|성분명 : 황기|분량 : 18.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램 중|성분명 : 목별자|분량 : 18.75|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '10그람중-발근고/1그램 중-고약', '수집URL': 'https://drug.hospitalk.net/item/197500291', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=197500291', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200400196', 'ITEM_NAME': '고려민지연질캡슐(은행엽엑스)(수출용)(수출명:유카민연질캡슐(은행엽엑스))', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은행엽엑스', 'ENTP_NAME': '(주)유유제약', 'CHART': '갈색 내용물이 들어있는 갈색의 타원형 연질캡슐', 'CHANGE_DATE': '2013-03-29', 'BAR_CODE': '8806445000801,8806445000818,8806445000825', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M080879]은행엽엑스', '함량_원료성분원문': '총량 : 이 약 1캡슐(666mg) 중|성분명 : 은행엽엑스|분량 : 40|단위 : 밀리그램|규격 : 생규|성분정보 : 총 깅고플라본배당체로서 9.6mg', '함량_총량기준': '이 약 1캡슐(666mg) 중', '수집URL': 'https://drug.hospitalk.net/item/200400196', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200400196', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198802731', 'ITEM_NAME': '고려삼분(홍삼가루)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '홍삼', 'ENTP_NAME': '(주)한국인삼공사', 'CHART': '담황갈색의 홍삼분말', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806785000103,8806785000110', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040784]홍삼', '함량_원료성분원문': '총량 : |성분명 : 홍삼|분량 : 1|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '미기재', '수집URL': 'https://drug.hospitalk.net/item/198802731', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198802731', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199101745', 'ITEM_NAME': '고려아시클로버크림(아시클로버)(수출명:바이락스크림(VIRAXCream)이노바이락스5%크림(INNOVIRAX5%Cream)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아시클로버', 'ENTP_NAME': '고려제약(주)', 'CHART': '전질이 고른 흰색의 크림제', 'CHANGE_DATE': '2020-08-25', 'BAR_CODE': '8806428001108,8806428001115,8806428001122', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081569]아시클로버', '함량_원료성분원문': '총량 : 1그램|성분명 : 아시클로버|분량 : 50.0|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/199101745', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199101745', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201205043', 'ITEM_NAME': '고운자임맘정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '토코페롤아세테이트 2배산;제피아스코르브산;폴산;리보플라빈;티아민질산염;니코틴산아미드;피리독신염산염;콜레칼시페롤농축분말;산화마그네슘;황산망간수화물;유비데카레논;시아노코발라민 1%;비오틴;판토텐산칼슘;푸마르산철;산화제이구리;산화아연', 'ENTP_NAME': '(주)종근당', 'CHART': '분홍색의 물방울형 필름코팅정', 'CHANGE_DATE': '2021-06-11', 'BAR_CODE': '8806433063405,8806433063412,8806433063429', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M255819]토코페롤아세테이트 2배산|[M236913]제피아스코르브산|[M223289]폴산|[M040133]리보플라빈|[M223262]티아민질산염|[M040064]니코틴산아미드|[M204304]피리독신염산염|[M102050]콜레칼시페롤농축분말|[M040262]산화마그네슘|[M246028]황산망간수화물|[M051233]유비데카레논|[M225607]시아노코발라민 1%|[M050704]비오틴|[M244748]판토텐산칼슘|[M051783]푸마르산철|[M246343]산화제이구리|[M243785]산화아연', '함량_원료성분원문': '총량 : 1정(769밀리그램) 중|성분명 : 유비데카레논|분량 : 10.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(769밀리그램) 중|성분명 : 시아노코발라민 1%|분량 : 1.80|단위 : 밀리그램|규격 : 별규|성분정보 : 시아노코발라민으로서 18ug;총량 : 1정(769밀리그램) 중|성분명 : 비오틴|분량 : 0.30|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1정(769밀리그램) 중|성분명 : 판토텐산칼슘|분량 : 10.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(769밀리그램) 중|성분명 : 푸마르산철|분량 : 106.49|단위 : 밀리그램|규격 : USP|성분정보 : 철로서 35mg;총량 : 1정(769밀리그램) 중|성분명 : 산화제이구리|분량 : 1.26|단위 : 밀리그램|규격 : KP|성분정보 : 구리로서 1mg;총량 : 1정(769밀리그램) 중|성분명 : 산화아연|분량 : 16.18|단위 : 밀리그램|규격 : KP|성분정보 : 아연으로서 13mg;총량 : 1정(769밀리그램) 중|성분명 : 황산망간수화물|분량 : 3.077|단위 : 밀리그램|규격 : USP|성분정보 : 망간으로서 1mg;총량 : 1정(769밀리그램) 중|성분명 : 산화마그네슘|분량 : 165.85|단위 : 밀리그램|규격 : KP|성분정보 : 마그네슘으로서 100mg;총량 : 1정(769밀리그램) 중|성분명 : 콜레칼시페롤농축분말|분량 : 5.00|단위 : 밀리그램|규격 : BP|성분정보 : 비타민D(으)로서 500 아이.유;총량 : 1정(769밀리그램) 중|성분명 : 토코페롤아세테이트 2배산|분량 : 60.00|단위 : 밀리그램|규격 : EP|성분정보 : 비타민E로서 30IU;총량 : 1정(769밀리그램) 중|성분명 : 제피아스코르브산|분량 : 205.13|단위 : 밀리그램|규격 : 별규|성분정보 : 아스코르브산으로서 200mg;총량 : 1정(769밀리그램) 중|성분명 : 폴산|분량 : 0.50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(769밀리그램) 중|성분명 : 리보플라빈|분량 : 1.60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(769밀리그램) 중|성분명 : 티아민질산염|분량 : 1.40|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(769밀리그램) 중|성분명 : 니코틴산아미드|분량 : 19.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(769밀리그램) 중|성분명 : 피리독신염산염|분량 : 2.00|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정(769밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201205043', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201205043', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201306109', 'ITEM_NAME': '고칼디정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '탄산칼슘;콜레칼시페롤농축분말', 'ENTP_NAME': '대화제약(주)', 'CHART': '녹색의 장방형 필름코팅정', 'CHANGE_DATE': '2022-11-24', 'BAR_CODE': '8806456042104,8806456042111,8806456042128', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051564]탄산칼슘|[M102050]콜레칼시페롤농축분말', '함량_원료성분원문': '총량 : 1정(1647.5mg) 중|성분명 : 탄산칼슘|분량 : 1250|단위 : 밀리그램|규격 : EP|성분정보 : 칼슘(으)로서 500 밀리그램;총량 : 1정(1647.5mg) 중|성분명 : 콜레칼시페롤농축분말|분량 : 10|단위 : 밀리그램|규격 : EP|성분정보 : 비타민D(으)로서 1000 아이.유', '함량_총량기준': '1정(1647.5mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201306109', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201306109', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198500873', 'ITEM_NAME': '고호환(양혈장근건보환)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '토사자;구기자;보골지;두충;방풍;산약;방기;백출;구판;강활;우슬;인삼;오미자;황기;작약;창출;황백;당귀;골쇄보;숙지황', 'ENTP_NAME': '익수제약(주)', 'CHART': '갈색의 환제이다.', 'CHANGE_DATE': '2015-06-23', 'BAR_CODE': '8806585000402,8806585000419,8806585000426,8806585000433,8806585000440,8806585000457,8806585000464,8806585000471,8806585000488,8806585000495,8806585015918,8806585015925', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050719]토사자|[M040030]구기자|[M050609]보골지|[M040089]두충|[M040205]방풍|[M040258]산약|[M050533]방기|[M040214]백출|[M080514]구판|[M050022]강활|[M040476]우슬|[M040213]인삼|[M040445]오미자|[M040790]황기|[M040523]작약|[M040548]창출|[M040793]황백|[M040070]당귀|[M086023]골쇄보|[M051364]숙지황|[M040213]인삼|[M040030]구기자|[M050609]보골지|[M040089]두충|[M040205]방풍|[M040258]산약|[M050533]방기|[M040214]백출|[M051364]숙지황|[M050719]토사자|[M080514]구판|[M050022]강활|[M040445]오미자|[M040790]황기|[M040523]작약|[M040548]창출|[M040793]황백|[M040070]당귀|[M086023]골쇄보|[M040476]우슬', '함량_원료성분원문': '총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 숙지황|분량 : 18.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 백출|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 방기|분량 : 6.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 산약|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 방풍|분량 : 6.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 두충|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 보골지|분량 : 12.5|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 구기자|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 토사자|분량 : 12.5|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 구판|분량 : 12.5|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 강활|분량 : 6.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 우슬|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 골쇄보|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 당귀|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 황백|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 창출|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 작약|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 황기|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 오미자|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 인삼|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 숙지황|분량 : 150|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 백출|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 방기|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 산약|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 방풍|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 두충|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 보골지|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 구기자|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 토사자|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 구판|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 강활|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 우슬|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 골쇄보|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 당귀|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 황백|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 창출|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 작약|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 황기|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 오미자|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중|성분명 : 인삼|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중-중환(412.5mg)/중환 (412.5mg) 중 / 소환 (3.3g, 100mg×33환) 중-소환(3.3g, 100mg X 33환)', '수집URL': 'https://drug.hospitalk.net/item/198500873', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198500873', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201305956', 'ITEM_NAME': '골드본드안티이치크림(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': 'L-멘톨;프라목신염산염', 'ENTP_NAME': '태극제약(주)', 'CHART': '백색 또는 미백색의 크림제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806448047100,8806448047117', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M279284]L-멘톨|[M246661]프라목신염산염|[M279284]L-멘톨|[M246661]프라목신염산염', '함량_원료성분원문': '총량 : 이 약 1그램 중|성분명 : L-멘톨|분량 : 10|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 이 약 1그램 중|성분명 : 프라목신염산염|분량 : 10|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 이 약 1그램 중|성분명 : L-멘톨|분량 : 10|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 이 약 1그램 중|성분명 : 프라목신염산염|분량 : 10|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '이 약 1그램 중-제1법/이 약 1그램 중-제2법', '수집URL': 'https://drug.hospitalk.net/item/201305956', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201305956', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200802314', 'ITEM_NAME': '골드타민연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '셀레늄가루 0.1%;산화아연;유비데카레논;β-카로틴현탁액30%;아스코르브산;토코페롤아세테이트', 'ENTP_NAME': '(주)서흥', 'CHART': '적갈색의 내용물을 함유한 암적색의 장방형 연질캡슐제', 'CHANGE_DATE': '2026-10-08', 'BAR_CODE': '8806796004008,8806796004015', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M248796]셀레늄가루 0.1%|[M243785]산화아연|[M051233]유비데카레논|[M250857]β-카로틴현탁액30%|[M258994]아스코르브산|[M223240]토코페롤아세테이트', '함량_원료성분원문': '총량 : 1캡슐1,576밀리그램|성분명 : 토코페롤아세테이트|분량 : 200|단위 : 밀리그램|규격 : KP|성분정보 : 비타민E로서 200I.U.;총량 : 1캡슐1,576밀리그램|성분명 : 아스코르브산|분량 : 500|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1캡슐1,576밀리그램|성분명 : β-카로틴현탁액30%|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : β-카로틴으로서 3mg;총량 : 1캡슐1,576밀리그램|성분명 : 유비데카레논|분량 : 5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐1,576밀리그램|성분명 : 산화아연|분량 : 17.43|단위 : 밀리그램|규격 : KP|성분정보 : 아연으로서 14mg;총량 : 1캡슐1,576밀리그램|성분명 : 셀레늄가루 0.1%|분량 : 25|단위 : 밀리그램|규격 : KP|성분정보 : 셀레늄으로서 25ug', '함량_총량기준': '11,576', '수집URL': 'https://drug.hospitalk.net/item/200802314', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200802314', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199902612', 'ITEM_NAME': '골사민캡슐(결정글루코사민황산염)(수출명 : NEOCOMIN)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '결정글루코사민황산염', 'ENTP_NAME': '신일제약(주)', 'CHART': '흰색내지 연한 노란갈색의 가루 또는 과립상이 들어있는 상부-빨간보라색, 하부-연한노란색의 경질캡슐제', 'CHANGE_DATE': '2011-07-25', 'BAR_CODE': '8806538000305,8806538000312,8806538000329,8806538000336,8806538000343,8806538000350,8806538000367,8806538000374,8806538000381', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M247626]결정글루코사민황산염', '함량_원료성분원문': '총량 : 1캡슐(477mg) 중|성분명 : 결정글루코사민황산염|분량 : 312.5|단위 : 밀리그램|규격 : EP|성분정보 : 글루코사민황산염으로서 250mg', '함량_총량기준': '1캡슐(477mg) 중', '수집URL': 'https://drug.hospitalk.net/item/199902612', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199902612', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200713607', 'ITEM_NAME': '공비환', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '창출;황금;석고;생강;지실;대추;작약;감초;신이;길경;치자;시호;승마;지모;맥문동;비파엽', 'ENTP_NAME': '(주)아이월드제약', 'CHART': '흑색의 환제', 'CHANGE_DATE': '2014-11-26', 'BAR_CODE': '8806696029507,8806696029514,8806696029521,8806696029538,8806696029545', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040548]창출|[M040789]황금|[M040279]석고|[M050752]생강|[M040536]지실|[M040071]대추|[M040523]작약|[M040006]감초|[M050897]신이|[M040048]길경|[M040564]치자|[M040336]시호|[M040329]승마|[M040535]지모|[M040139]맥문동|[M082529]비파엽', '함량_원료성분원문': '총량 : 1회용량(2.1g)중|성분명 : 길경|분량 : 2.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 치자|분량 : 0.10|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 시호|분량 : 0.10|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 승마|분량 : 0.10|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 지모|분량 : 0.10|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 맥문동|분량 : 0.10|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 비파엽|분량 : 0.10|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 신이|분량 : 1.00|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 감초|분량 : 1.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 작약|분량 : 1.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 대추|분량 : 1.50|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 지실|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 생강|분량 : 1.00|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 석고|분량 : 1.00|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 황금|분량 : 0.10|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.1g)중|성분명 : 창출|분량 : 0.10|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1회용량(2.1g)중', '수집URL': 'https://drug.hospitalk.net/item/200713607', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200713607', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '196300084', 'ITEM_NAME': '광동경옥고', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '생지황즙;복령가루;인삼;꿀', 'ENTP_NAME': '광동제약(주)', 'CHART': '흑갈색의 점도가 있는 연조엑스제', 'CHANGE_DATE': '2023-07-13', 'BAR_CODE': '8806418000906,8806418000913,8806418000920,8806418000937,8806418060405,8806418060412,8806418060429,8806418065202,8806418065219,8806418065226,8806418065301,8806418065318,8806418065325,8806418065332,8806418065349,8806418065356,8806418065363,8806418065370,8806418065387', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M082091]생지황즙|[M082760]복령가루|[M051291]인삼|[M200168]꿀', '함량_원료성분원문': '총량 : 117.5그램|성분명 : 생지황즙|분량 : 39.9|단위 : 그램|규격 : 별규|성분정보 : ;총량 : 117.5그램|성분명 : 복령가루|분량 : 12.4|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 117.5그램|성분명 : 인삼|분량 : 6.2|단위 : 그램|규격 : KP|성분정보 : ;총량 : 117.5그램|성분명 : 꿀|분량 : 41.5|단위 : 그램|규격 : JP|성분정보 :', '함량_총량기준': '117.5', '수집URL': 'https://drug.hospitalk.net/item/196300084', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=196300084', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201800548', 'ITEM_NAME': '광동경옥고(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '꿀;인삼;복령가루;생지황즙', 'ENTP_NAME': '광동제약(주)', 'CHART': '흑갈색의 점도가 있는 연조엑스제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806418065509,8806418065516', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M200168]꿀|[M040213]인삼|[M082760]복령가루|[M082091]생지황즙', '함량_원료성분원문': '총량 : 100그램|성분명 : 생지황즙|분량 : 39.9|단위 : 그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 100그램|성분명 : 복령가루|분량 : 12.4|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 100그램|성분명 : 인삼|분량 : 6.2|단위 : 그램|규격 : KP|성분정보 : ;총량 : 100그램|성분명 : 꿀|분량 : 41.5|단위 : 그램|규격 : JP|성분정보 :', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/201800548', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201800548', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200301909', 'ITEM_NAME': '광동공진단', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '숙지황;인삼;사향;산수유;당귀;녹용', 'ENTP_NAME': '광동제약(주)', 'CHART': '황금색 금박을 입힌 구형의 환제', 'CHANGE_DATE': '2013-07-04', 'BAR_CODE': '8806418001101,8806418001118,8806418001125,8806418001132,8806418001149,8806418001156,8806418001163,8806418001170,8806418001187,8806418001194,8806418073412,8806418073429,8806418073436,8806418073443,8806418073450', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051364]숙지황|[M040213]인삼|[M040253]사향|[M040257]산수유|[M040070]당귀|[M050139]녹용', '함량_원료성분원문': '총량 : 1환(3.95g)중|성분명 : 녹용|분량 : 444.4|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.95g)중|성분명 : 당귀|분량 : 444.4|단위 : 밀리그램|규격 : KP|성분정보 : 총 데쿠르신으로서 0.026g;총량 : 1환(3.95g)중|성분명 : 산수유|분량 : 444.4|단위 : 밀리그램|규격 : KP|성분정보 : 로가닌으로서 2.22mg;총량 : 1환(3.95g)중|성분명 : 사향|분량 : 74.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.95g)중|성분명 : 인삼|분량 : 444.4|단위 : 밀리그램|규격 : KP|성분정보 : 진세노시드 Rb1으로서 0.89mg;총량 : 1환(3.95g)중|성분명 : 숙지황|분량 : 444.4|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1환(3.95g)중', '수집URL': 'https://drug.hospitalk.net/item/200301909', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200301909', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200402781', 'ITEM_NAME': '광동금탕액(향갈탕)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '향갈탕연조엑스', 'ENTP_NAME': '광동제약(주)', 'CHART': '특이한 생약취가 있는 약간 혼탁한 갈색의 액제', 'CHANGE_DATE': '2010-04-09', 'BAR_CODE': '8806418001309,8806418001316', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M085445]향갈탕연조엑스', '함량_원료성분원문': '총량 : 1병100밀리리터|성분명 : 향갈탕연조엑스|분량 : 3.75|단위 : 그램|규격 : 별규|성분정보 :', '함량_총량기준': '1100', '수집URL': 'https://drug.hospitalk.net/item/200402781', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200402781', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200402786', 'ITEM_NAME': '광동동의한방고카타플라스마', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '토코페롤아세테이트;글리시리진산;d-캄파;L-멘톨;살리실산글리콜;산초30%에탄올연조엑스(3.3→1);치자연조엑스(3.0→1);황백연조엑스(3.3→1)', 'ENTP_NAME': '광동제약(주)', 'CHART': '이 약은 미황적색의 점착성 고체를 부직포위에 도포한 방향성을 가진 카타플라스마와 별도로 밀착포가 첨부된 카타플라스마제', 'CHANGE_DATE': '2025-08-29', 'BAR_CODE': '8806418001804,8806418001811', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223240]토코페롤아세테이트|[M050096]글리시리진산|[M204418]d-캄파|[M279284]L-멘톨|[M070611]살리실산글리콜|[M209235]산초30%에탄올연조엑스(3.3→1)|[M207935]치자연조엑스(3.0→1)|[M213350]황백연조엑스(3.3→1)', '함량_원료성분원문': '총량 : 1매(10×14cm2, 14g) 중|성분명 : 황백연조엑스(3.3→1)|분량 : 98.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1매(10×14cm2, 14g) 중|성분명 : 치자연조엑스(3.0→1)|분량 : 46.2|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1매(10×14cm2, 14g) 중|성분명 : 산초30%에탄올연조엑스(3.3→1)|분량 : 42.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1매(10×14cm2, 14g) 중|성분명 : 살리실산글리콜|분량 : 280.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1매(10×14cm2, 14g) 중|성분명 : L-멘톨|분량 : 140.0|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1매(10×14cm2, 14g) 중|성분명 : d-캄파|분량 : 70.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1매(10×14cm2, 14g) 중|성분명 : 글리시리진산|분량 : 4.2|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1매(10×14cm2, 14g) 중|성분명 : 토코페롤아세테이트|분량 : 42.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1매(10×14cm2, 14g) 중', '수집URL': 'https://drug.hospitalk.net/item/200402786', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200402786', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201600289', 'ITEM_NAME': '광동리버샷정(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '리보플라빈;우르소데옥시콜산;간가수분해물(4→1)', 'ENTP_NAME': '광동제약(주)', 'CHART': '특이한 방향을 가진 적갈색의 원형 필름코팅정제', 'CHANGE_DATE': '2025-07-01', 'BAR_CODE': '8806418062003,8806418062010,8806418062027', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040133]리보플라빈|[M223167]우르소데옥시콜산|[M261840]간가수분해물(4→1)', '함량_원료성분원문': '총량 : 1정(228밀리그램중)|성분명 : 간가수분해물(4→1)|분량 : 100.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1정(228밀리그램중)|성분명 : 우르소데옥시콜산|분량 : 8.33|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(228밀리그램중)|성분명 : 리보플라빈|분량 : 2.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정(228밀리그램중)', '수집URL': 'https://drug.hospitalk.net/item/201600289', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201600289', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202004494', 'ITEM_NAME': '광동리버샷정300(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '리보플라빈;우르소데옥시콜산;간가수분해물(4→1)', 'ENTP_NAME': '광동제약(주)', 'CHART': '특이한 방향을 가진 적갈색의 장방형 필름코팅정', 'CHANGE_DATE': '2025-01-02', 'BAR_CODE': '8806418069408,8806418069415', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040133]리보플라빈|[M223167]우르소데옥시콜산|[M261840]간가수분해물(4→1)', '함량_원료성분원문': '총량 : 1정684밀리그램|성분명 : 간가수분해물(4→1)|분량 : 300.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1정684밀리그램|성분명 : 우르소데옥시콜산|분량 : 24.99|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정684밀리그램|성분명 : 리보플라빈|분량 : 6.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1684', '수집URL': 'https://drug.hospitalk.net/item/202004494', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202004494', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199302420', 'ITEM_NAME': '광동마음정액(청심보혈탕)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '진피;생지황;천궁;맥문동;산조인초;복신;작약초;인삼;치자초;감초초;오미자;당귀', 'ENTP_NAME': '광동제약(주)', 'CHART': '이 약은 특이한 냄새를 가진 약간 혼탁한 갈색의 액제이다.', 'CHANGE_DATE': '2023-05-03', 'BAR_CODE': '8806418008001,8806418008018,8806418008025', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040538]진피|[M051363]생지황|[M040550]천궁|[M040139]맥문동|[M064512]산조인초|[M081401]복신|[M090789]작약초|[M051291]인삼|[M085737]치자초|[M236652]감초초|[M040445]오미자|[M040070]당귀', '함량_원료성분원문': '총량 : 이 약 1병(50mL) 중|성분명 : 인삼|분량 : 1.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 이 약 1병(50mL) 중|성분명 : 치자초|분량 : 0.62|단위 : 그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 이 약 1병(50mL) 중|성분명 : 감초초|분량 : 0.62|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 이 약 1병(50mL) 중|성분명 : 오미자|분량 : 0.39|단위 : 그램|규격 : KP|성분정보 : ;총량 : 이 약 1병(50mL) 중|성분명 : 당귀|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 이 약 1병(50mL) 중|성분명 : 작약초|분량 : 1.25|단위 : 그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 이 약 1병(50mL) 중|성분명 : 복신|분량 : 1.25|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 이 약 1병(50mL) 중|성분명 : 산조인초|분량 : 1.25|단위 : 그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 이 약 1병(50mL) 중|성분명 : 맥문동|분량 : 1.25|단위 : 그램|규격 : KP|성분정보 : ;총량 : 이 약 1병(50mL) 중|성분명 : 천궁|분량 : 0.62|단위 : 그램|규격 : KP|성분정보 : ;총량 : 이 약 1병(50mL) 중|성분명 : 생지황|분량 : 0.62|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 이 약 1병(50mL) 중|성분명 : 진피|분량 : 0.62|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 1병(50mL) 중', '수집URL': 'https://drug.hospitalk.net/item/199302420', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199302420', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201802148', 'ITEM_NAME': '광동만수고골드플라스타', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': 'l-멘톨;dl-캄파;토코페롤아세테이트;황백연조엑스 (3.3→1);치자연조엑스 (3.0→1);살리실산글리콜', 'ENTP_NAME': '광동제약(주)', 'CHART': '이 약은 미황색 내지 황색의 약액을 고체피복물상에 도포하고 고체면에 지지체를 덮은 특이한 냄새가 있는 첩부제이다.', 'CHANGE_DATE': '2025-08-29', 'BAR_CODE': '8806418066209,8806418066216,8806418066223,8806418066308,8806418066315,8806418066322', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M230875]l-멘톨|[M204423]dl-캄파|[M223240]토코페롤아세테이트|[M243794]황백연조엑스 (3.3→1)|[M243795]치자연조엑스 (3.0→1)|[M070611]살리실산글리콜|[M243795]치자연조엑스 (3.0→1)|[M070611]살리실산글리콜|[M230875]l-멘톨|[M204423]dl-캄파|[M223240]토코페롤아세테이트|[M243794]황백연조엑스 (3.3→1)', '함량_원료성분원문': '총량 : 1처방 1매(10×14㎠,140㎠, 5.20g)중|성분명 : 살리실산글리콜|분량 : 160.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1처방 1매(10×14㎠,140㎠, 5.20g)중|성분명 : l-멘톨|분량 : 160.00|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1처방 1매(10×14㎠,140㎠, 5.20g)중|성분명 : dl-캄파|분량 : 80.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1처방 1매(10×14㎠,140㎠, 5.20g)중|성분명 : 토코페롤아세테이트|분량 : 48.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1처방 1매(10×14㎠,140㎠, 5.20g)중|성분명 : 황백연조엑스 (3.3→1)|분량 : 112.00|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1처방 1매(10×14㎠,140㎠, 5.20g)중|성분명 : 치자연조엑스 (3.0→1)|분량 : 52.80|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 2처방 1매(10×7㎠,70㎠, 2.60g)중|성분명 : 살리실산글리콜|분량 : 80.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 2처방 1매(10×7㎠,70㎠, 2.60g)중|성분명 : l-멘톨|분량 : 80.00|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 2처방 1매(10×7㎠,70㎠, 2.60g)중|성분명 : dl-캄파|분량 : 40.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 2처방 1매(10×7㎠,70㎠, 2.60g)중|성분명 : 토코페롤아세테이트|분량 : 24.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 2처방 1매(10×7㎠,70㎠, 2.60g)중|성분명 : 황백연조엑스 (3.3→1)|분량 : 56.00|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 2처방 1매(10×7㎠,70㎠, 2.60g)중|성분명 : 치자연조엑스 (3.0→1)|분량 : 26.40|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1처방 1매(10×14㎠,140㎠, 5.20g)중/2처방 1매(10×7㎠,70㎠, 2.60g)중', '수집URL': 'https://drug.hospitalk.net/item/201802148', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201802148', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201701095', 'ITEM_NAME': '광동벤포파워액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '벤포티아민;니코틴산아미드;피리독신염산염;리보플라빈;산화아연;우르소데옥시콜산', 'ENTP_NAME': '광동제약(주)', 'CHART': '특이한 향이 있는 황색의 맑은 액제', 'CHANGE_DATE': '2022-01-18', 'BAR_CODE': '8806418062805,8806418062812', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M096428]벤포티아민|[M040064]니코틴산아미드|[M204304]피리독신염산염|[M040133]리보플라빈|[M243785]산화아연|[M223167]우르소데옥시콜산', '함량_원료성분원문': '총량 : 100mL 중|성분명 : 벤포티아민|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : 티아민염산염으로서 36.15mg;총량 : 100mL 중|성분명 : 니코틴산아미드|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100mL 중|성분명 : 피리독신염산염|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 :  ;총량 : 100mL 중|성분명 : 리보플라빈|분량 : 9.4|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100mL 중|성분명 : 산화아연|분량 : 12.466|단위 : 밀리그램|규격 : KP|성분정보 : 아연으로 10mg;총량 : 100mL 중|성분명 : 우르소데옥시콜산|분량 : 10.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '100mL 중', '수집URL': 'https://drug.hospitalk.net/item/201701095', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201701095', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201903344', 'ITEM_NAME': '광동벤포파워제트액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '우르소데옥시콜산;산화아연;리보플라빈;피리독신염산염;니코틴산아미드;벤포티아민', 'ENTP_NAME': '광동제약(주)', 'CHART': '갈색의 유리병에 든 특이한 향이 있는 황색의 맑은 액제', 'CHANGE_DATE': '2023-08-02', 'BAR_CODE': '8806418067503,8806418067510', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223167]우르소데옥시콜산|[M244641]산화아연|[M040133]리보플라빈|[M204304]피리독신염산염|[M040064]니코틴산아미드|[M096428]벤포티아민', '함량_원료성분원문': '총량 : 1병100밀리리터|성분명 : 벤포티아민|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : 티아민염산염(으)로서 36.15 밀리그램;총량 : 1병100밀리리터|성분명 : 니코틴산아미드|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 피리독신염산염|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 리보플라빈|분량 : 9.4|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 산화아연|분량 : 24.932|단위 : 밀리그램|규격 : JP|성분정보 : 아연(으)로서 20 밀리그램;총량 : 1병100밀리리터|성분명 : 우르소데옥시콜산|분량 : 10.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1100', '수집URL': 'https://drug.hospitalk.net/item/201903344', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201903344', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201005178', 'ITEM_NAME': '광동비타민A유연질캡슐(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '비타민A유', 'ENTP_NAME': '광동제약(주)', 'CHART': '황색-황갈색의 유액이 충전된 청색의 투명한 연질캡슐제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806418049905', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040249]비타민A유', '함량_원료성분원문': '총량 : 1캡슐(410밀리그램) 중|성분명 : 비타민A유|분량 : 100,000|단위 : 아이.유|규격 : USP|성분정보 :', '함량_총량기준': '1캡슐(410밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201005178', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201005178', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201005179', 'ITEM_NAME': '광동비타민A유연질캡슐20만아이유(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '비타민A유', 'ENTP_NAME': '광동제약(주)', 'CHART': '황색-황갈색의 유액이 충전된 황색의 투명한 연질캅셀제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806418050000', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040249]비타민A유', '함량_원료성분원문': '총량 : 1캡슐(410밀리그램) 중|성분명 : 비타민A유|분량 : 200,000|단위 : 아이.유|규격 : USP|성분정보 :', '함량_총량기준': '1캡슐(410밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201005179', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201005179', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198601266', 'ITEM_NAME': '광동쌍화탕(수출명:파인트리쌍화탕)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '쌍화탕연조엑스', 'ENTP_NAME': '광동제약(주)', 'CHART': '특이한 생약취를 가진 흑갈색의 액체로서 약간 혼탁하다.', 'CHANGE_DATE': '2024-03-26', 'BAR_CODE': '8806418005208,8806418005215,8806418005222', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M086603]쌍화탕연조엑스', '함량_원료성분원문': '총량 : 1병100밀리리터|성분명 : 쌍화탕연조엑스|분량 : 4.2|단위 : 그램|규격 : 별규|성분정보 :', '함량_총량기준': '1100', '수집URL': 'https://drug.hospitalk.net/item/198601266', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198601266', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201702015', 'ITEM_NAME': '광동아스피린장용정100mg', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아스피린', 'ENTP_NAME': '광동제약(주)', 'CHART': '흰색의 원형 장용성 필름코팅정', 'CHANGE_DATE': '2025-04-15', 'BAR_CODE': '8806418062904,8806418062911,8806418062928', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040355]아스피린', '함량_원료성분원문': '총량 : 1정(157mg) 중|성분명 : 아스피린|분량 : 100.0|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '1정(157mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201702015', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201702015', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201907347', 'ITEM_NAME': '광동알디액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '로얄젤리;D-판테놀;티아민질산염;토코페롤아세테이트;피리독신염산염;니코틴산아미드;리보플라빈', 'ENTP_NAME': '광동제약(주)', 'CHART': '갈색 유리병에 든 특이한 향이 있는 황색의 액제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806418068203,8806418068210', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M200412]로얄젤리|[M202582]D-판테놀|[M223262]티아민질산염|[M223240]토코페롤아세테이트|[M204304]피리독신염산염|[M040064]니코틴산아미드|[M040133]리보플라빈', '함량_원료성분원문': '총량 : 1병100밀리리터|성분명 : 리보플라빈|분량 : 3.9|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 니코틴산아미드|분량 : 10.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 피리독신염산염|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 토코페롤아세테이트|분량 : 30.0|단위 : 밀리그램|규격 : KP|성분정보 : 비타민E로서30IU;총량 : 1병100밀리리터|성분명 : 티아민질산염|분량 : 30.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : D-판테놀|분량 : 30.0|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 로얄젤리|분량 : 50.0|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1100', '수집URL': 'https://drug.hospitalk.net/item/201907347', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201907347', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201002981', 'ITEM_NAME': '광동알벤다졸정(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '알벤다졸', 'ENTP_NAME': '광동제약(주)', 'CHART': '장방형의 분홍색 필름코팅정', 'CHANGE_DATE': '2020-04-02', 'BAR_CODE': '8806418048908', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081226]알벤다졸', '함량_원료성분원문': '총량 : 1정(630밀리그램) 중|성분명 : 알벤다졸|분량 : 400|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1정(630밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201002981', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201002981', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202201218', 'ITEM_NAME': '광동에너릭정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시아노코발라민;피리독신염산염;티아민질산염;카페인무수물', 'ENTP_NAME': '광동제약(주)', 'CHART': '은색 펄이 있는 옅은 갈색의 원형 필름코팅정', 'CHANGE_DATE': '2024-12-11', 'BAR_CODE': '8806418071302,8806418071319', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M096429]시아노코발라민|[M204304]피리독신염산염|[M223262]티아민질산염|[M223183]카페인무수물', '함량_원료성분원문': '총량 : 1정300밀리그램|성분명 : 카페인무수물|분량 : 100.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정300밀리그램|성분명 : 티아민질산염|분량 : 2.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정300밀리그램|성분명 : 피리독신염산염|분량 : 2.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정300밀리그램|성분명 : 시아노코발라민|분량 : 3.75|단위 : 마이크로그램|규격 : KP|성분정보 :', '함량_총량기준': '1300', '수집URL': 'https://drug.hospitalk.net/item/202201218', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202201218', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198601268', 'ITEM_NAME': '광동우황청심원', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '사향;용뇌;백렴;건강;인삼;포황;신곡;대두황권;육계;작약;맥문동;영양각;아교;감초;산약;황금;당귀;방풍;백출;시호;길경;행인;복령;천궁;우황', 'ENTP_NAME': '광동제약(주)', 'CHART': '황금색 금박을 입힌 구형의 환제이다.', 'CHANGE_DATE': '2022-05-30', 'BAR_CODE': '8806418006502,8806418006519,8806418006526,8806418006533', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040253]사향|[M051197]용뇌|[M050541]백렴|[M040007]건강|[M040213]인삼|[M051762]포황|[M050891]신곡|[M050191]대두황권|[M050036]육계|[M040523]작약|[M040139]맥문동|[M051133]영양각|[M050905]아교|[M040006]감초|[M040258]산약|[M040789]황금|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040336]시호|[M040048]길경|[M040769]행인|[M040225]복령|[M040550]천궁|[M040478]우황', '함량_원료성분원문': '총량 : 1환(3.75g) 중|성분명 : 산약|분량 : 282|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 황금|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 당귀|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : 총데쿠르신으로 3.54mg;총량 : 1환(3.75g) 중|성분명 : 방풍|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 백출|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 시호|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 길경|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 행인|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : 아미그달린으로서 1.5mg;총량 : 1환(3.75g) 중|성분명 : 복령|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 천궁|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 우황|분량 : 14|단위 : 밀리그램|규격 : JP|성분정보 : 결합형 빌리루빈으로서 2.80mg;총량 : 1환(3.75g) 중|성분명 : 감초|분량 : 202|단위 : 밀리그램|규격 : KP|성분정보 : 글리시리진산으로서 5.05mg;총량 : 1환(3.75g) 중|성분명 : 아교|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 영양각|분량 : 35|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 사향|분량 : 5|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 용뇌|분량 : 41|단위 : 밀리그램|규격 : 생규|성분정보 : 이소보르네올 및 놀보르네올로서 38.58mg;총량 : 1환(3.75g) 중|성분명 : 백렴|분량 : 30|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 건강|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 인삼|분량 : 97|단위 : 밀리그램|규격 : KP|성분정보 : 진세노시드Rb1으로서 0.19mg;총량 : 1환(3.75g) 중|성분명 : 포황|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 신곡|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 대두황권|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g) 중|성분명 : 육계|분량 : 70|단위 : 밀리그램|규격 : KP|성분정보 : 신남산으로서 21.0㎍;총량 : 1환(3.75g) 중|성분명 : 작약|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : 패오니플로린으로서 1.2mg;총량 : 1환(3.75g) 중|성분명 : 맥문동|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1환(3.75g) 중', '수집URL': 'https://drug.hospitalk.net/item/198601268', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198601268', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200102705', 'ITEM_NAME': '광동우황청심원(사향대체물질영묘향함유)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '영묘향;용뇌;백렴;건강;인삼;포황;신곡;대두황권;육계;작약;맥문동;영양각;아교;감초;황금;당귀;방풍;백출;시호;길경;행인;복령;천궁;우황;산약', 'ENTP_NAME': '광동제약(주)', 'CHART': '황금색 금박을 입힌 구형의 환제', 'CHANGE_DATE': '2011-02-18', 'BAR_CODE': '8806418006601,8806418006618,8806418006625,8806418006632', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M085197]영묘향|[M051197]용뇌|[M050541]백렴|[M040007]건강|[M040213]인삼|[M051762]포황|[M050891]신곡|[M050191]대두황권|[M050036]육계|[M040523]작약|[M040139]맥문동|[M051133]영양각|[M050905]아교|[M040006]감초|[M040789]황금|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040336]시호|[M040048]길경|[M040769]행인|[M040225]복령|[M040550]천궁|[M040478]우황|[M040258]산약', '함량_원료성분원문': '총량 : 1환(3.75g)중|성분명 : 산약|분량 : 282|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 황금|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 당귀|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 방풍|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 백출|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 시호|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 길경|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 행인|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 복령|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 천궁|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 우황|분량 : 14|단위 : 밀리그램|규격 : JP|성분정보 : 결합형 빌리루빈으로서 2.80밀리그램;총량 : 1환(3.75g)중|성분명 : 감초|분량 : 202|단위 : 밀리그램|규격 : KP|성분정보 : 글리시리진산으로서 5.05밀리그램;총량 : 1환(3.75g)중|성분명 : 아교|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 영양각|분량 : 35|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 영묘향|분량 : 15|단위 : 밀리그램|규격 : 별규|성분정보 : 9-cis-civetone으로서 81.0㎍;총량 : 1환(3.75g)중|성분명 : 용뇌|분량 : 41|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 백렴|분량 : 30|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 건강|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 인삼|분량 : 97|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 포황|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 신곡|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 대두황권|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 육계|분량 : 70|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 작약|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75g)중|성분명 : 맥문동|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1환(3.75g)중', '수집URL': 'https://drug.hospitalk.net/item/200102705', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200102705', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199102319', 'ITEM_NAME': '광동우황청심원(수출용)(수출명:동방우황청심원)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '용뇌;백렴;생강;대추;인삼;포황;신곡;대두황권;육계;작약;맥문동;사향;영양각;감초;산약;황금;당귀;방풍;백출;시호;길경;복령;천궁;우황;아교', 'ENTP_NAME': '광동제약(주)', 'CHART': '황금색 금박을 입힌 구형의 환제', 'CHANGE_DATE': '2023-06-22', 'BAR_CODE': '8806418006700,8806418006717,8806418006724', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051197]용뇌|[M050541]백렴|[M050752]생강|[M040071]대추|[M040213]인삼|[M051762]포황|[M050891]신곡|[M050191]대두황권|[M050036]육계|[M040523]작약|[M040139]맥문동|[M040253]사향|[M051133]영양각|[M040006]감초|[M040258]산약|[M040789]황금|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040336]시호|[M040048]길경|[M040225]복령|[M040550]천궁|[M040478]우황|[M050905]아교', '함량_원료성분원문': '총량 : 1환(3.534g)|성분명 : 산약|분량 : 450.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1환(3.534g)|성분명 : 황금|분량 : 110.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1환(3.534g)|성분명 : 당귀|분량 : 110.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1환(3.534g)|성분명 : 방풍|분량 : 120.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1환(3.534g)|성분명 : 백출|분량 : 110.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1환(3.534g)|성분명 : 시호|분량 : 80.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1환(3.534g)|성분명 : 길경|분량 : 80.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1환(3.534g)|성분명 : 복령|분량 : 84.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1환(3.534g)|성분명 : 천궁|분량 : 180.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1환(3.534g)|성분명 : 우황|분량 : 30.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1환(3.534g)|성분명 : 아교|분량 : 130.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1환(3.534g)|성분명 : 감초|분량 : 320.0|단위 : 밀리그램|규격 : JP|성분정보 : 글리시리진산으로서 8.9~20.8 밀리그램;총량 : 1환(3.534g)|성분명 : 영양각|분량 : 215.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1환(3.534g)|성분명 : 사향|분량 : 5.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1환(3.534g)|성분명 : 용뇌|분량 : 90.0|단위 : 밀리그램|규격 : 별규|성분정보 : 총-보르네올(Nor-보르네올 및 Iso-보르네올)으로서 81.5~99.6 밀리그램;총량 : 1환(3.534g)|성분명 : 백렴|분량 : 46.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1환(3.534g)|성분명 : 생강|분량 : 46.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1환(3.534g)|성분명 : 대추|분량 : 150.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1환(3.534g)|성분명 : 인삼|분량 : 160.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1환(3.534g)|성분명 : 포황|분량 : 160.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1환(3.534g)|성분명 : 신곡|분량 : 160.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1환(3.534g)|성분명 : 대두황권|분량 : 130.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1환(3.534g)|성분명 : 육계|분량 : 130.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1환(3.534g)|성분명 : 작약|분량 : 110.0|단위 : 밀리그램|규격 : JP|성분정보 : 패오니플로린으로서 2.2~5.2 밀리그램;총량 : 1환(3.534g)|성분명 : 맥문동|분량 : 110.0|단위 : 밀리그램|규격 : JP|성분정보 :', '함량_총량기준': '1환(3.534g)', '수집URL': 'https://drug.hospitalk.net/item/199102319', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199102319', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200604296', 'ITEM_NAME': '광동우황청심원과립(사향대체물질영묘향함유)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '인삼;우황;용뇌;영묘향;감초;포황;신곡;대두황권;계피;작약;맥문동;건강;백렴;아교;산약;황금;당귀;방풍;백출;시호;길경;행인;복령;천궁;영양각', 'ENTP_NAME': '광동제약(주)', 'CHART': '회갈색 내지 흑갈색의 과립제', 'CHANGE_DATE': '2024-03-21', 'BAR_CODE': '8806418006809,8806418006816,8806418006823,8806418006830', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051291]인삼|[M040478]우황|[M051197]용뇌|[M085197]영묘향|[M040006]감초|[M090765]포황|[M050891]신곡|[M050191]대두황권|[M040016]계피|[M040523]작약|[M040139]맥문동|[M040007]건강|[M050541]백렴|[M050905]아교|[M040258]산약|[M040789]황금|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040336]시호|[M040048]길경|[M040769]행인|[M040225]복령|[M040550]천궁|[M051133]영양각', '함량_원료성분원문': '총량 : 1포800밀리그램|성분명 : 산약|분량 : 282|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 황금|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 당귀|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 방풍|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 백출|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 시호|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 길경|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 행인|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 복령|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 천궁|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 영양각|분량 : 35|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포800밀리그램|성분명 : 아교|분량 : 70|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1포800밀리그램|성분명 : 백렴|분량 : 30|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포800밀리그램|성분명 : 건강|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 영묘향|분량 : 15|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1포800밀리그램|성분명 : 용뇌|분량 : 41|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포800밀리그램|성분명 : 우황|분량 : 14|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 인삼|분량 : 97|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 감초|분량 : 202|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 포황|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포800밀리그램|성분명 : 신곡|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포800밀리그램|성분명 : 대두황권|분량 : 70|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포800밀리그램|성분명 : 계피|분량 : 70|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 작약|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포800밀리그램|성분명 : 맥문동|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1800', '수집URL': 'https://drug.hospitalk.net/item/200604296', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200604296', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199102325', 'ITEM_NAME': '광동우황청심원현탁액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '사향;용뇌;백렴;건강;인삼;포황;신곡;대두황권;육계;작약;맥문동;영양각;아교;감초;산약;황금;당귀;방풍;백출;시호;길경;행인;복령;천궁;우황', 'ENTP_NAME': '광동제약(주)', 'CHART': '갈색의 특이한 방향성의 불투명 현탁제', 'CHANGE_DATE': '2013-11-13', 'BAR_CODE': '8806418006908,8806418006915,8806418006922', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040253]사향|[M051197]용뇌|[M050541]백렴|[M040007]건강|[M040213]인삼|[M051762]포황|[M050891]신곡|[M050191]대두황권|[M050036]육계|[M040523]작약|[M040139]맥문동|[M051133]영양각|[M050905]아교|[M040006]감초|[M040258]산약|[M040789]황금|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040336]시호|[M040048]길경|[M040769]행인|[M040225]복령|[M040550]천궁|[M040478]우황', '함량_원료성분원문': '총량 : 50밀리리터|성분명 : 산약|분량 : 282.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 황금|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 당귀|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 방풍|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 백출|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 시호|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 길경|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 행인|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 복령|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 천궁|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 우황|분량 : 14.0|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 50밀리리터|성분명 : 감초|분량 : 202.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 아교|분량 : 70.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 50밀리리터|성분명 : 영양각|분량 : 35.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 50밀리리터|성분명 : 사향|분량 : 5|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 50밀리리터|성분명 : 용뇌|분량 : 41.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 50밀리리터|성분명 : 백렴|분량 : 30.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 50밀리리터|성분명 : 건강|분량 : 30.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 인삼|분량 : 97.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 포황|분량 : 100.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 50밀리리터|성분명 : 신곡|분량 : 100.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 50밀리리터|성분명 : 대두황권|분량 : 70.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 50밀리리터|성분명 : 육계|분량 : 70.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 작약|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 50밀리리터|성분명 : 맥문동|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '50', '수집URL': 'https://drug.hospitalk.net/item/199102325', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199102325', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199902843', 'ITEM_NAME': '광동우황청심원현탁액(사향대체물질영묘향함유)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시호;방풍;인삼;복령;백출;용뇌;영양각;아교;신곡;백렴;대두황권;맥문동;육계;황금;행인;영묘향;포황;천궁;작약;우황;감초;건강;길경;당귀;산약', 'ENTP_NAME': '광동제약(주)', 'CHART': '갈색의 특이한 방향성의 불투명한 현탁액제', 'CHANGE_DATE': '2009-05-28', 'BAR_CODE': '8806418007004,8806418007011,8806418007028,8806418007035', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040336]시호|[M040205]방풍|[M040213]인삼|[M040225]복령|[M040214]백출|[M051197]용뇌|[M051133]영양각|[M050905]아교|[M050891]신곡|[M050541]백렴|[M050191]대두황권|[M040139]맥문동|[M050036]육계|[M040789]황금|[M040769]행인|[M085197]영묘향|[M051762]포황|[M040550]천궁|[M040523]작약|[M040478]우황|[M040006]감초|[M040007]건강|[M040048]길경|[M040070]당귀|[M040258]산약|[M040789]황금|[M040205]방풍|[M040213]인삼|[M040225]복령|[M040214]백출|[M051197]용뇌|[M051133]영양각|[M050905]아교|[M050891]신곡|[M050541]백렴|[M050191]대두황권|[M040258]산약|[M040336]시호|[M040139]맥문동|[M040769]행인|[M085197]영묘향|[M051762]포황|[M040550]천궁|[M040523]작약|[M040478]우황|[M040006]감초|[M040007]건강|[M040048]길경|[M040070]당귀|[M050036]육계', '함량_원료성분원문': '총량 : 1병30밀리리터|성분명 : 산약|분량 : 282.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병30밀리리터|성분명 : 대두황권|분량 : 70.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병30밀리리터|성분명 : 백렴|분량 : 30.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병30밀리리터|성분명 : 신곡|분량 : 100.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병30밀리리터|성분명 : 아교|분량 : 70.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병30밀리리터|성분명 : 영양각|분량 : 35.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병30밀리리터|성분명 : 용뇌|분량 : 41.0|단위 : 밀리그램|규격 : 생규|성분정보 :  ;총량 : 1병30밀리리터|성분명 : 백출|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병30밀리리터|성분명 : 복령|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병30밀리리터|성분명 : 인삼|분량 : 97.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병30밀리리터|성분명 : 방풍|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병30밀리리터|성분명 : 시호|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병30밀리리터|성분명 : 맥문동|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병30밀리리터|성분명 : 육계|분량 : 70.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병30밀리리터|성분명 : 당귀|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병30밀리리터|성분명 : 길경|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병30밀리리터|성분명 : 건강|분량 : 30.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병30밀리리터|성분명 : 감초|분량 : 202.0|단위 : 밀리그램|규격 : KP|성분정보 :  ;총량 : 1병30밀리리터|성분명 : 우황|분량 : 14.0|단위 : 밀리그램|규격 : JP|성분정보 :  ;총량 : 1병30밀리리터|성분명 : 작약|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병30밀리리터|성분명 : 천궁|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병30밀리리터|성분명 : 포황|분량 : 100.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병30밀리리터|성분명 : 영묘향|분량 : 15.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1병30밀리리터|성분명 : 행인|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병30밀리리터|성분명 : 황금|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 산약|분량 : 282.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 대두황권|분량 : 70.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 백렴|분량 : 30.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 신곡|분량 : 100.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 아교|분량 : 70.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 영양각|분량 : 35.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 용뇌|분량 : 41.0|단위 : 밀리그램|규격 : 생규|성분정보 :  ;총량 : 1병50밀리리터|성분명 : 백출|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 복령|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 인삼|분량 : 97.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 방풍|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 시호|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 맥문동|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 육계|분량 : 70.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 당귀|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 길경|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 건강|분량 : 30.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 감초|분량 : 202.0|단위 : 밀리그램|규격 : KP|성분정보 :  ;총량 : 1병50밀리리터|성분명 : 우황|분량 : 14.0|단위 : 밀리그램|규격 : JP|성분정보 :  ;총량 : 1병50밀리리터|성분명 : 작약|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 천궁|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 포황|분량 : 100.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 영묘향|분량 : 15.0|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1병50밀리리터|성분명 : 행인|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 황금|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '130/150', '수집URL': 'https://drug.hospitalk.net/item/199902843', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199902843', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '197300231', 'ITEM_NAME': '광동원방우황청심원', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건강;백렴;용뇌;사향;인삼;포황;신곡;대두황권;육계;작약;맥문동;영양각;아교;감초;산약;황금;당귀;방풍;백출;시호;길경;행인;복령;천궁;우황', 'ENTP_NAME': '광동제약(주)', 'CHART': '황금색 금박을 입힌 구형의 환제', 'CHANGE_DATE': '2023-07-05', 'BAR_CODE': '8806418007103,8806418007110', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040007]건강|[M050541]백렴|[M051197]용뇌|[M040253]사향|[M040213]인삼|[M051762]포황|[M050891]신곡|[M050191]대두황권|[M050036]육계|[M040523]작약|[M040139]맥문동|[M051133]영양각|[M050905]아교|[M040006]감초|[M040258]산약|[M040789]황금|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040336]시호|[M040048]길경|[M040769]행인|[M040225]복령|[M040550]천궁|[M040478]우황', '함량_원료성분원문': '총량 : 1환(7.5g) 중|성분명 : 산약|분량 : 263|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 황금|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 당귀|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 방풍|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 백출|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 시호|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 길경|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 행인|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 복령|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 천궁|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 우황|분량 : 45|단위 : 밀리그램|규격 : JP|성분정보 : 결합형빌리루빈으로서 9.0mg;총량 : 1환(7.5g) 중|성분명 : 감초|분량 : 188|단위 : 밀리그램|규격 : KP|성분정보 : 글리시리진산으로서 4.7mg;총량 : 1환(7.5g) 중|성분명 : 아교|분량 : 66|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 영양각|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 사향|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 용뇌|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 백렴|분량 : 28|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 건강|분량 : 28|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 인삼|분량 : 94|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 포황|분량 : 94|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 신곡|분량 : 94|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 대두황권|분량 : 66|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 육계|분량 : 66|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 작약|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 맥문동|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1환(7.5g) 중', '수집URL': 'https://drug.hospitalk.net/item/197300231', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=197300231', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200102707', 'ITEM_NAME': '광동원방우황청심원(사향대체물질영묘향함유)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '맥문동;영묘향;용뇌;백렴;건강;인삼;포황;신곡;대두황권;육계;작약;영양각;아교;감초;산약;황금;당귀;방풍;백출;시호;길경;행인;복령;천궁;우황', 'ENTP_NAME': '광동제약(주)', 'CHART': '황금색 금박을 입힌 구형의 환제', 'CHANGE_DATE': '2011-02-18', 'BAR_CODE': '8806418007301,8806418007318,8806418007325', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040139]맥문동|[M085197]영묘향|[M051197]용뇌|[M050541]백렴|[M040007]건강|[M040213]인삼|[M051762]포황|[M050891]신곡|[M050191]대두황권|[M050036]육계|[M040523]작약|[M051133]영양각|[M050905]아교|[M040006]감초|[M040258]산약|[M040789]황금|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040336]시호|[M040048]길경|[M040769]행인|[M040225]복령|[M040550]천궁|[M040478]우황', '함량_원료성분원문': '총량 : 1환(7.5g) 중|성분명 : 산약|분량 : 263|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 황금|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 당귀|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 방풍|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 백출|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 시호|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 길경|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 행인|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 복령|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 천궁|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 우황|분량 : 45|단위 : 밀리그램|규격 : JP|성분정보 : 결합형빌리루빈으로서 9.0mg;총량 : 1환(7.5g) 중|성분명 : 감초|분량 : 188|단위 : 밀리그램|규격 : KP|성분정보 : 글리시리진산으로서 4.7mg;총량 : 1환(7.5g) 중|성분명 : 아교|분량 : 66|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 영양각|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 영묘향|분량 : 114|단위 : 밀리그램|규격 : 별규|성분정보 : 영묘향 9-cis-civetone으로서 615.6㎍;총량 : 1환(7.5g) 중|성분명 : 용뇌|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 백렴|분량 : 28|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 건강|분량 : 28|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 인삼|분량 : 94|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 포황|분량 : 94|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 신곡|분량 : 94|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 대두황권|분량 : 66|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 육계|분량 : 66|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 작약|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(7.5g) 중|성분명 : 맥문동|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1환(7.5g) 중', '수집URL': 'https://drug.hospitalk.net/item/200102707', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200102707', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199401702', 'ITEM_NAME': '광동원방우황청심원현탁액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '사향;용뇌;백렴;건강;인삼;포황;신곡;대두황권;육계;작약;맥문동;영양각;아교;감초;산약;황금;당귀;방풍;백출;시호;길경;행인;복령;천궁;우황', 'ENTP_NAME': '광동제약(주)', 'CHART': '갈색의 특이한 방향성의 불투명 현탁제', 'CHANGE_DATE': '2013-11-13', 'BAR_CODE': '8806418007400,8806418007417', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040253]사향|[M051197]용뇌|[M050541]백렴|[M040007]건강|[M040213]인삼|[M051762]포황|[M050891]신곡|[M050191]대두황권|[M050036]육계|[M040523]작약|[M040139]맥문동|[M051133]영양각|[M050905]아교|[M040006]감초|[M040258]산약|[M040789]황금|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040336]시호|[M040048]길경|[M040769]행인|[M040225]복령|[M040550]천궁|[M040478]우황', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 산약|분량 : 526|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 황금|분량 : 112|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 당귀|분량 : 112|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 방풍|분량 : 112|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 백출|분량 : 112|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 시호|분량 : 94|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 길경|분량 : 94|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 행인|분량 : 94|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 복령|분량 : 94|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 천궁|분량 : 94|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 우황|분량 : 90|단위 : 밀리그램|규격 : JP|성분정보 :  ;총량 : 100밀리리터|성분명 : 감초|분량 : 376|단위 : 밀리그램|규격 : KP|성분정보 :  ;총량 : 100밀리리터|성분명 : 아교|분량 : 132|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 100밀리리터|성분명 : 영양각|분량 : 76|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 100밀리리터|성분명 : 사향|분량 : 76|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 100밀리리터|성분명 : 용뇌|분량 : 76|단위 : 밀리그램|규격 : 생규|성분정보 :  ;총량 : 100밀리리터|성분명 : 백렴|분량 : 56|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 100밀리리터|성분명 : 건강|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 인삼|분량 : 188|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 포황|분량 : 188|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 100밀리리터|성분명 : 신곡|분량 : 188|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 100밀리리터|성분명 : 대두황권|분량 : 132|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 100밀리리터|성분명 : 육계|분량 : 132|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 작약|분량 : 112|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 맥문동|분량 : 112|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/199401702', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199401702', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199902844', 'ITEM_NAME': '광동원방우황청심원현탁액(사향대체물질영묘향함유)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건강;백렴;용뇌;영묘향;인삼;포황;신곡;대두황권;육계;작약;맥문동;영양각;아교;감초;산약;황금;당귀;방풍;백출;시호;길경;행인;복령;천궁;우황', 'ENTP_NAME': '광동제약(주)', 'CHART': '갈색의 특이한 방향성의 불투명 현탁액제', 'CHANGE_DATE': '2009-04-30', 'BAR_CODE': '8806418007509,8806418007516', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040007]건강|[M050541]백렴|[M051197]용뇌|[M085197]영묘향|[M040213]인삼|[M051762]포황|[M050891]신곡|[M050191]대두황권|[M050036]육계|[M040523]작약|[M040139]맥문동|[M051133]영양각|[M050905]아교|[M040006]감초|[M040258]산약|[M040789]황금|[M040070]당귀|[M040205]방풍|[M040214]백출|[M040336]시호|[M040048]길경|[M040769]행인|[M040225]복령|[M040550]천궁|[M040478]우황', '함량_원료성분원문': '총량 : 1병50밀리리터|성분명 : 산약|분량 : 263|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 황금|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 당귀|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 방풍|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 백출|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 시호|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 길경|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 행인|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 복령|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 천궁|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 우황|분량 : 45|단위 : 밀리그램|규격 : JP|성분정보 :  ;총량 : 1병50밀리리터|성분명 : 감초|분량 : 188|단위 : 밀리그램|규격 : KP|성분정보 :  ;총량 : 1병50밀리리터|성분명 : 아교|분량 : 66|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 영양각|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 영묘향|분량 : 114|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : ;총량 : 1병50밀리리터|성분명 : 용뇌|분량 : 38|단위 : 밀리그램|규격 : 생규|성분정보 :  ;총량 : 1병50밀리리터|성분명 : 백렴|분량 : 28|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 건강|분량 : 28|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 인삼|분량 : 94|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 포황|분량 : 94|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 신곡|분량 : 94|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 대두황권|분량 : 66|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1병50밀리리터|성분명 : 육계|분량 : 66|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 작약|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 맥문동|분량 : 56|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '150', '수집URL': 'https://drug.hospitalk.net/item/199902844', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199902844', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199401699', 'ITEM_NAME': '광동원탕', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '원탕연조엑스', 'ENTP_NAME': '광동제약(주)', 'CHART': '특이한 생약취를 가진 약간 혼탁한 흑갈색의 액제', 'CHANGE_DATE': '2024-04-22', 'BAR_CODE': '8806418007608,8806418007615', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M095974]원탕연조엑스', '함량_원료성분원문': '총량 : 1병100밀리리터|성분명 : 원탕연조엑스|분량 : 5.25|단위 : 그램|규격 : 별규|성분정보 :', '함량_총량기준': '1100', '수집URL': 'https://drug.hospitalk.net/item/199401699', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199401699', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202302073', 'ITEM_NAME': '광동인후엔가글액(포비돈요오드)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '포비돈요오드', 'ENTP_NAME': '광동제약(주)', 'CHART': '황갈색의 가글제', 'CHANGE_DATE': '2025-04-01', 'BAR_CODE': '8806418074600,8806418074617', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M244708]포비돈요오드', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 포비돈요오드|분량 : 0.35|단위 : 그램|규격 : USP|성분정보 : 유효요오드(으)로서 0.035 그램', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/202302073', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202302073', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202107393', 'ITEM_NAME': '광동자강력연조엑스(쌍화탕연조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '쌍화탕 연조엑스', 'ENTP_NAME': '광동제약(주)', 'CHART': '이 약은 알루미늄 호일 스틱 포에 담긴 특이한 생약취를 가진 흑갈색의 연조엑스제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806418071104,8806418071111,8806418071128', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M110678]쌍화탕 연조엑스', '함량_원료성분원문': '총량 : 1포15그램|성분명 : 쌍화탕 연조엑스|분량 : 4.2|단위 : 그램|규격 : 별규|성분정보 :', '함량_총량기준': '115', '수집URL': 'https://drug.hospitalk.net/item/202107393', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202107393', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199202176', 'ITEM_NAME': '광동장원정(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '생건지황주세;석창포;산조인초;백자인거유;원지강제;당귀주세;현삼;용안육;맥문동;인삼;복신', 'ENTP_NAME': '광동제약(주)', 'CHART': '이 약은 녹색의 장방형 필림코팅정이다.', 'CHANGE_DATE': '2022-08-05', 'BAR_CODE': '8806418007707,8806418007714', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050123]생건지황주세|[M051377]석창포|[M064512]산조인초|[M084847]백자인거유|[M085177]원지강제|[M082382]당귀주세|[M051932]현삼|[M051200]용안육|[M040139]맥문동|[M051291]인삼|[M081401]복신', '함량_원료성분원문': '총량 : 1정 중 470밀리그램|성분명 : 복신|분량 : 31.3|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1정 중 470밀리그램|성분명 : 인삼|분량 : 31.3|단위 : 밀리그램|규격 : KP|성분정보 : Ginsenoside Rb₁로서 62.6마이크로그램;총량 : 1정 중 470밀리그램|성분명 : 맥문동|분량 : 31.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 중 470밀리그램|성분명 : 용안육|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 중 470밀리그램|성분명 : 현삼|분량 : 47|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 중 470밀리그램|성분명 : 당귀주세|분량 : 31.3|단위 : 밀리그램|규격 : 별규|성분정보 : Decursin으로서 1.8밀리그램;총량 : 1정 중 470밀리그램|성분명 : 원지강제|분량 : 47|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1정 중 470밀리그램|성분명 : 백자인거유|분량 : 31.3|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1정 중 470밀리그램|성분명 : 산조인초|분량 : 31.3|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1정 중 470밀리그램|성분명 : 석창포|분량 : 47|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1정 중 470밀리그램|성분명 : 생건지황주세|분량 : 47|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1정 중 470밀리그램', '수집URL': 'https://drug.hospitalk.net/item/199202176', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199202176', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202204148', 'ITEM_NAME': '광동치올페이스트(히노키티올)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '히노키티올', 'ENTP_NAME': '광동제약(주)', 'CHART': '특이한 향이 있는 미황색의 페이스트제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806418072200,8806418072217,8806418072705,8806418072712,8806418073306,8806418073313,8806418074808,8806418074815', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M202166]히노키티올', '함량_원료성분원문': '총량 : 1그램|성분명 : 히노키티올|분량 : 1.0|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/202204148', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202204148', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202301522', 'ITEM_NAME': '광동침옥고', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '꿀;침향 가루;구기자 가루;복령 가루;인삼 가루;생지황즙', 'ENTP_NAME': '광동제약(주)', 'CHART': '이 약은 흑갈색의 유동성 연조엑스상의 물질로서 특이한 냄새가 있고 맛은 달고 조금 쓰다. 이 약은 물에 조금 혼탁시켜 녹이면 유갈색의 액이 된다.', 'CHANGE_DATE': '미기재', 'BAR_CODE': '미기재', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M200168]꿀|[M110568]침향 가루|[M111107]구기자 가루|[M110385]복령 가루|[M110386]인삼 가루|[M082091]생지황즙', '함량_원료성분원문': '총량 : 100그램|성분명 : 생지황즙|분량 : 32.0|단위 : 그램|규격 : 별규|성분정보 : ;총량 : 100그램|성분명 : 인삼 가루|분량 : 2.8|단위 : 그램|규격 : 별규|성분정보 : ;총량 : 100그램|성분명 : 복령 가루|분량 : 8.0|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 100그램|성분명 : 구기자 가루|분량 : 0.9|단위 : 그램|규격 : 별규|성분정보 : ;총량 : 100그램|성분명 : 침향 가루|분량 : 0.1|단위 : 그램|규격 : 별규|성분정보 : ;총량 : 100그램|성분명 : 꿀|분량 : 38.5|단위 : 그램|규격 : 별규|성분정보 :', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/202301522', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202301522', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202500617', 'ITEM_NAME': '광동칼디정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '티아민염산염;폴산;콜레칼시페롤농축분말;시트르산칼슘수화물', 'ENTP_NAME': '광동제약(주)', 'CHART': '분홍색의 장방형 필름코팅정', 'CHANGE_DATE': '2025-12-26', 'BAR_CODE': '8806418073900,8806418073917,8806418073924', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223258]티아민염산염|[M223289]폴산|[M102050]콜레칼시페롤농축분말|[M247470]시트르산칼슘수화물', '함량_원료성분원문': '총량 : 1정645밀리그램|성분명 : 시트르산칼슘수화물|분량 : 475|단위 : 밀리그램|규격 : USP|성분정보 : 칼슘(으)로서 100.11 밀리그램;총량 : 1정645밀리그램|성분명 : 콜레칼시페롤농축분말|분량 : 10|단위 : 밀리그램|규격 : EP|성분정보 : 비타민D(으)로서 1,000 아이.유;총량 : 1정645밀리그램|성분명 : 폴산|분량 : 1|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정645밀리그램|성분명 : 티아민염산염|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1645', '수집URL': 'https://drug.hospitalk.net/item/202500617', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202500617', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202501561', 'ITEM_NAME': '광동콜에스액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '카페인무수물;클로르페니라민말레산염;에페드린염산염;구아이페네신;아세트아미노펜', 'ENTP_NAME': '광동제약(주)', 'CHART': '갈색 유리병에 든 무색 또는 미황색의 투명한 액제', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806418074709,8806418074716', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223183]카페인무수물|[M223211]클로르페니라민말레산염|[M223155]에페드린염산염|[M050058]구아이페네신|[M040353]아세트아미노펜', '함량_원료성분원문': '총량 : 1병50밀리리터|성분명 : 아세트아미노펜|분량 : 300|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 구아이페네신|분량 : 83.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 에페드린염산염|분량 : 17.5|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 클로르페니라민말레산염|분량 : 2.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병50밀리리터|성분명 : 카페인무수물|분량 : 30.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '150', '수집URL': 'https://drug.hospitalk.net/item/202501561', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202501561', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201404328', 'ITEM_NAME': '광동탕에이액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아세트아미노펜;작약;대추;육계;건강;감초', 'ENTP_NAME': '광동제약(주)', 'CHART': '특이한 생약취를 가진 엷은 갈색의 액제', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806418057603,8806418057610,8806418059706,8806418059713', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040353]아세트아미노펜|[M040523]작약|[M040071]대추|[M050036]육계|[M040007]건강|[M040006]감초', '함량_원료성분원문': '총량 : 1병100밀리리터|성분명 : 감초|분량 : 133.4|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 건강|분량 : 66.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 육계|분량 : 266.8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 대추|분량 : 266.8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 작약|분량 : 266.8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 아세트아미노펜|분량 : 200.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1100', '수집URL': 'https://drug.hospitalk.net/item/201404328', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201404328', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201908635', 'ITEM_NAME': '광동탕엠액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아세트아미노펜;마황;행인;육계;감초', 'ENTP_NAME': '광동제약(주)', 'CHART': '갈색의 유리병에 든 특이한 생약취를 가진 갈색의 액제', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806418068609,8806418068616', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040353]아세트아미노펜|[M040135]마황|[M040769]행인|[M050036]육계|[M040006]감초', '함량_원료성분원문': '총량 : 1병100밀리리터|성분명 : 감초|분량 : 133.8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 육계|분량 : 200.8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 행인|분량 : 267.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 마황|분량 : 267.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병100밀리리터|성분명 : 아세트아미노펜|분량 : 200.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1100', '수집URL': 'https://drug.hospitalk.net/item/201908635', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201908635', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200908059', 'ITEM_NAME': '광동파워센액(시트룰린말산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시트룰린말산염', 'ENTP_NAME': '광동제약(주)', 'CHART': '오렌지향의 무색 내지 엷은 황색의 액', 'CHANGE_DATE': '2022-05-12', 'BAR_CODE': '8806418047109,8806418047116', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M247305]시트룰린말산염', '함량_원료성분원문': '총량 : 1병30밀리리터|성분명 : 시트룰린말산염|분량 : 1.0|단위 : 그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '130', '수집URL': 'https://drug.hospitalk.net/item/200908059', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200908059', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201603402', 'ITEM_NAME': '광동푸로스판시럽(아이비엽30% 에탄올엑스(5∼7.5→1))', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아이비엽30%에탄올엑스(5~7.5→1)', 'ENTP_NAME': '광동제약(주)', 'CHART': '독특한 향이 들어있는 맑은 갈색의 현탁 시럽제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806418062409,8806418062416', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M217121]아이비엽30%에탄올엑스(5~7.5→1)', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 아이비엽30%에탄올엑스(5~7.5→1)|분량 : 700.0|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/201603402', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201603402', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201402679', 'ITEM_NAME': '광동프라목신크림(프라목신염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '프라목신염산염', 'ENTP_NAME': '광동제약(주)', 'CHART': '흰색의 크림제', 'CHANGE_DATE': '2019-07-08', 'BAR_CODE': '8806418056200,8806418056217', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M246661]프라목신염산염', '함량_원료성분원문': '총량 : 1그램|성분명 : 프라목신염산염|분량 : 10|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/201402679', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201402679', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198601263', 'ITEM_NAME': '광진환(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대추;건강;백렴;용뇌;인삼;포황;신곡;대두황권;육계;아교;작약;영양각;우황;감초;산약;맥문동;황금;당귀;방풍;창출;시호;길경;행인;복령;천궁', 'ENTP_NAME': '광동제약(주)', 'CHART': '황금색 금박을 입힌 구형의 환제', 'CHANGE_DATE': '2022-08-05', 'BAR_CODE': '8806418006403', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040071]대추|[M040007]건강|[M050541]백렴|[M051197]용뇌|[M051291]인삼|[M090765]포황|[M050891]신곡|[M050191]대두황권|[M050036]육계|[M050905]아교|[M040523]작약|[M051133]영양각|[M040478]우황|[M040006]감초|[M040258]산약|[M040139]맥문동|[M040789]황금|[M040070]당귀|[M040205]방풍|[M040548]창출|[M040336]시호|[M040048]길경|[M040769]행인|[M040225]복령|[M040550]천궁', '함량_원료성분원문': '총량 : 1환(3.75그램)중|성분명 : 산약|분량 : 131.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 맥문동|분량 : 28.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 황금|분량 : 28.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 당귀|분량 : 28.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 방풍|분량 : 28.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 창출|분량 : 28.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 시호|분량 : 23.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 길경|분량 : 23.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 행인|분량 : 23.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 복령|분량 : 23.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 천궁|분량 : 22.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 감초|분량 : 93.75|단위 : 밀리그램|규격 : KP|성분정보 : glycyrrhizin 4.2밀리그램;총량 : 1환(3.75그램)중|성분명 : 우황|분량 : 22.5|단위 : 밀리그램|규격 : KP|성분정보 : 결합형 빌리루빈으로서 2.3밀리그램;총량 : 1환(3.75그램)중|성분명 : 영양각|분량 : 18.75|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 용뇌|분량 : 18.75|단위 : 밀리그램|규격 : 생규|성분정보 : 총-보르네올(Iso-보르네올 및 Nor-보르네올)로서 17.6밀리그램;총량 : 1환(3.75그램)중|성분명 : 백렴|분량 : 14.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 건강|분량 : 14.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 대추|분량 : 120.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 인삼|분량 : 46.875|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 포황|분량 : 46.875|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 신곡|분량 : 46.875|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 대두황권|분량 : 32.75|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 육계|분량 : 32.75|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 아교|분량 : 32.75|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환(3.75그램)중|성분명 : 작약|분량 : 28.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1환(3.75그램)중', '수집URL': 'https://drug.hospitalk.net/item/198601263', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198601263', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200904078', 'ITEM_NAME': '구로칼캡슐(결정글루코사민황산염)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '결정글루코사민황산염', 'ENTP_NAME': '(주)동구바이오제약', 'CHART': '흰색 내지 엷은 담황색 가루가 들어있는 상부 연녹색, 하부 연녹색 경질캡슐', 'CHANGE_DATE': '2019-08-05', 'BAR_CODE': '8806573046702,8806573046719', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M247626]결정글루코사민황산염', '함량_원료성분원문': '총량 : 1캡슐477밀리그램|성분명 : 결정글루코사민황산염|분량 : 312.5|단위 : 밀리그램|규격 : EP|성분정보 :', '함량_총량기준': '1477', '수집URL': 'https://drug.hospitalk.net/item/200904078', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200904078', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200904818', 'ITEM_NAME': '구로칼캡슐500mg(결정글루코사민황산염)(수출명:GUROCAL 500mg CAPSULE)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '결정글루코사민황산염', 'ENTP_NAME': '(주)동구바이오제약', 'CHART': '제법1 : 흰색 내지 담황색의 가루 또는 과립상이 든 상부적색, 하부 미황색의 경질캡슐 제법2 : 흰색의 가루 또는 과립상이 든 상하부 암갈색의 경질캡슐', 'CHANGE_DATE': '2015-04-14', 'BAR_CODE': '8806573047303,8806573047310', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M247626]결정글루코사민황산염|[M247626]결정글루코사민황산염', '함량_원료성분원문': '총량 : 제법1 : 1캡슐(900mg) 중, 제법2 : 1캡슐(729mg) 중|성분명 : 결정글루코사민황산염|분량 : 625|단위 : 밀리그램|규격 : KPC|성분정보 : 글루코사민황산염으로서500mg;총량 : 제법1 : 1캡슐(900mg) 중, 제법2 : 1캡슐(729mg) 중|성분명 : 결정글루코사민황산염|분량 : 625|단위 : 밀리그램|규격 : KPC|성분정보 : 글루코사민황산염으로서 500mg', '함량_총량기준': '제법1 : 1캡슐(900mg) 중, 제법2 : 1캡슐(729mg) 중-제법1/제법1 : 1캡슐(900mg) 중, 제법2 : 1캡슐(729mg) 중-제법2', '수집URL': 'https://drug.hospitalk.net/item/200904818', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200904818', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201502890', 'ITEM_NAME': '구루치온정100밀리그램(글루타티온(환원형))', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '글루타티온(환원형)', 'ENTP_NAME': '영풍제약(주)', 'CHART': '흰색의 원형 당의정', 'CHANGE_DATE': '2015-06-09', 'BAR_CODE': '8806619045409,8806619045416,8806619045423,8806619045430', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256276]글루타티온(환원형)', '함량_원료성분원문': '총량 : 1정450.33밀리그램|성분명 : 글루타티온(환원형)|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1450.33', '수집URL': 'https://drug.hospitalk.net/item/201502890', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201502890', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202602701', 'ITEM_NAME': '구미슬림산', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건강;감초;목단피;반하;대황;승마;작약;택사;저령;육계;시호', 'ENTP_NAME': '(주)마더스제약', 'CHART': '담갈색의 산제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806228058302,8806228058319,8806228058326', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040007]건강|[M040006]감초|[M040185]목단피|[M040202]반하|[M040073]대황|[M040329]승마|[M040523]작약|[M040638]택사|[M051313]저령|[M050036]육계|[M040336]시호', '함량_원료성분원문': '총량 : 1포2.3그램|성분명 : 시호|분량 : 286|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 육계|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 저령|분량 : 286|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 택사|분량 : 286|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 작약|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 승마|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 대황|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 반하|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 목단피|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 감초|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포2.3그램|성분명 : 건강|분량 : 143|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '12.3', '수집URL': 'https://drug.hospitalk.net/item/202602701', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202602701', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201800233', 'ITEM_NAME': '구미포비돈세정액7.5%(포비돈요오드)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '포비돈요오드', 'ENTP_NAME': '구미제약(주)', 'CHART': '황갈색의 액제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806804002606,8806804002613,8806804002620', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M244694]포비돈요오드', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 포비돈요오드|분량 : 7.5|단위 : 그램|규격 : KP|성분정보 : 요오드(으)로서 750 밀리그램', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/201800233', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201800233', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200203626', 'ITEM_NAME': '구미포비돈요오드액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '포비돈 요오드', 'ENTP_NAME': '구미제약(주)', 'CHART': '황갈색의 액체', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806804000800,8806804000817,8806804000824,8806804000831,8806804000848,8806804000855', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M215884]포비돈 요오드', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 포비돈 요오드|분량 : 10|단위 : 그램|규격 : KP|성분정보 : 유효요오드로서 1그램', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/200203626', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200203626', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200302817', 'ITEM_NAME': '구미포비스왑스틱(포비돈요오드)(수출명:포비딕)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '포비돈 요오드', 'ENTP_NAME': '구미제약(주)', 'CHART': '황갈색의 액을 흡착시킨 면봉', 'CHANGE_DATE': '2019-07-22', 'BAR_CODE': '8806804000909,8806804000916,8806804000923,8806804000930', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M215884]포비돈 요오드', '함량_원료성분원문': '총량 : 약액1.5밀리리터중|성분명 : 포비돈 요오드|분량 : 0.15|단위 : 그램|규격 : KP|성분정보 : 유효요오드로서 15밀리그램', '함량_총량기준': '약액1.5밀리리터중-탈지면봉1개(0.9그램)당(탈지면0.2그램)약액1.5밀리리터를흡착/흡착제1개중-탈지면봉1개(0.9그램)당(탈지면0.2그램)약액1.5밀리리터를흡착', '수집URL': 'https://drug.hospitalk.net/item/200302817', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200302817', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202601939', 'ITEM_NAME': '구미헥시1%에타외용액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '에탄올;클로르헥시딘글루콘산염 액', 'ENTP_NAME': '구미제약(주)', 'CHART': '제1처방- 백색의 반투명 내지 불투명한 로션제 제2처방- 향긋한 냄새가 나는 백색의 반투명 내지 불투명한 로션제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806804003504,8806804003511,8806804003603,8806804003610', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089677]에탄올|[M223220]클로르헥시딘글루콘산염 액|[M089677]에탄올|[M223220]클로르헥시딘글루콘산염 액', '함량_원료성분원문': '총량 : 100그램|성분명 : 에탄올|분량 : 65.78|단위 : 그램|규격 : USP|성분정보 : 에탄올(으)로서 60.8 그램;총량 : 100그램|성분명 : 클로르헥시딘글루콘산염 액|분량 : 5.325|단위 : 그램|규격 : KP|성분정보 : 글루콘산클로르헥시딘(으)로서 1.0 그램;총량 : 100그램|성분명 : 에탄올|분량 : 65.78|단위 : 그램|규격 : USP|성분정보 : 에탄올(으)로서 60.8 그램;총량 : 100그램|성분명 : 클로르헥시딘글루콘산염 액|분량 : 5.325|단위 : 그램|규격 : KP|성분정보 : 글루콘산클로르헥시딘(으)로서 1.0 그램', '함량_총량기준': '100/100', '수집URL': 'https://drug.hospitalk.net/item/202601939', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202601939', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202001153', 'ITEM_NAME': '구미헥시에탄올스틱스왑액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염 액;에탄올(95)', 'ENTP_NAME': '구미제약(주)', 'CHART': '(제 1처방) 특이한 향 및 알콜냄새가 나는 무색의 투명한 액체가 흡착된 탈지면봉 (제 2처방) 특이한 향 및 알콜냄새가 나는 적색의 투명한 액체가 흡착된 탈지면봉', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806804003108,8806804003115,8806804003122', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223220]클로르헥시딘글루콘산염 액|[M284425]에탄올(95)|[M223220]클로르헥시딘글루콘산염 액|[M284425]에탄올(95)', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 클로르헥시딘글루콘산염 액|분량 : 10|단위 : 밀리리터|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 에탄올(95)|분량 : 75|단위 : 밀리리터|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 클로르헥시딘글루콘산염 액|분량 : 10|단위 : 밀리리터|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 에탄올(95)|분량 : 75|단위 : 밀리리터|규격 : KP|성분정보 :', '함량_총량기준': '100-제 1처방(무색):약액/탈지면봉 1개 중(탈지면 0.2g + 약액 1.75mL 흡착)-제 1처방(무색):흡착제/100-제 2처방(붉은색):약액/탈지면봉 1개 중(탈지면 0.2g + 약액 1.75mL 흡착)-제 2처방(붉은색):흡착제', '수집URL': 'https://drug.hospitalk.net/item/202001153', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202001153', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201800284', 'ITEM_NAME': '구미헥시이소프로필스틱스왑액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염 액;이소프로판올', 'ENTP_NAME': '구미제약(주)', 'CHART': '특이한 향 및 알코올 냄새가 나는 무색의 투명한 액체가 흡착된 탈지면봉', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806804002705,8806804002712,8806804002729', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223220]클로르헥시딘글루콘산염 액|[M099850]이소프로판올', '함량_원료성분원문': '총량 : 탈지면봉 1개 중(탈지면 0.2g + 약액 1.75mL 흡착), 약액 1.75mL 중,|성분명 : 클로르헥시딘글루콘산염 액|분량 : 0.175|단위 : 밀리리터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염으로 35mg;총량 : 탈지면봉 1개 중(탈지면 0.2g + 약액 1.75mL 흡착), 약액 1.75mL 중,|성분명 : 이소프로판올|분량 : 1.225|단위 : 밀리리터|규격 : KP|성분정보 :', '함량_총량기준': '탈지면봉 1개 중(탈지면 0.2g + 약액 1.75mL 흡착), 약액 1.75mL 중,', '수집URL': 'https://drug.hospitalk.net/item/201800284', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201800284', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202500973', 'ITEM_NAME': '구미헥시크린가글0.12%액(클로르헥시딘글루콘산염액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염 액', 'ENTP_NAME': '구미제약(주)', 'CHART': '방향성을 지닌 무색 투명한 액제', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806804003405,8806804003412,8806804003429', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223220]클로르헥시딘글루콘산염 액', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 클로르헥시딘글루콘산염 액|분량 : 0.6|단위 : 밀리리터|규격 : BP|성분정보 : 클로르헥시딘글루콘산염(으)로서 0.12 그램', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/202500973', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202500973', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200812020', 'ITEM_NAME': '구미헥시크린브러쉬액(클로르헥시딘글루콘산염액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염 액', 'ENTP_NAME': '구미제약(주)', 'CHART': '향긋한 냄새가  나는 주홍색의 액체가 흡착된 프라스틱솔 스폰지', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806804002408,8806804002415,8806804002422', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223220]클로르헥시딘글루콘산염 액', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 클로르헥시딘글루콘산염 액|분량 : 20.0|단위 : 밀리리터|규격 : KP|성분정보 : 글루콘산클로르헥시딘으로서 4그램', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/200812020', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200812020', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200801346', 'ITEM_NAME': '구미헥시크린에이액(글루콘산클로르헥시딘액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '글루콘산클로르헥시딘액', 'ENTP_NAME': '구미제약(주)', 'CHART': '향긋한 냄새가 나는 주홍색의 투명한 액', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806804001807,8806804001814,8806804001821', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M243030]글루콘산클로르헥시딘액|[M243030]글루콘산클로르헥시딘액', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 글루콘산클로르헥시딘액|분량 : 25.0|단위 : 밀리리터|규격 : KP|성분정보 : 글루콘산클로르헥시딘으로서5그램;총량 : 100밀리리터|성분명 : 글루콘산클로르헥시딘액|분량 : 25.0|단위 : 밀리리터|규격 : KP|성분정보 : 글루콘산클로르헥시딘으로서5그램', '함량_총량기준': '100/100', '수집URL': 'https://drug.hospitalk.net/item/200801346', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200801346', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201903835', 'ITEM_NAME': '구미헥시크린에타2%액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염 액;에탄올(95)', 'ENTP_NAME': '구미제약(주)', 'CHART': '제 1처방 : 무색의 알코올 냄새가 나는 맑은 액 제 2처방 : 붉은색의 알코올 냄새가 나는 맑은 액 제 3처방 : 파란색의 알코올 냄새가 나는 맑은 액', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806804003009,8806804003016,8806804003023', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223220]클로르헥시딘글루콘산염 액|[M284425]에탄올(95)|[M223220]클로르헥시딘글루콘산염 액|[M284425]에탄올(95)|[M223220]클로르헥시딘글루콘산염 액|[M284425]에탄올(95)', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 클로르헥시딘글루콘산염 액|분량 : 10|단위 : 밀리리터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염(으)로서 2 그램;총량 : 100밀리리터|성분명 : 에탄올(95)|분량 : 75|단위 : 밀리리터|규격 : KP|성분정보 : 에탄올(으)로서 72 밀리리터;총량 : 100밀리리터|성분명 : 클로르헥시딘글루콘산염 액|분량 : 10|단위 : 밀리리터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염(으)로서 2 그램;총량 : 100밀리리터|성분명 : 에탄올(95)|분량 : 75|단위 : 밀리리터|규격 : KP|성분정보 : 에탄올(으)로서 72 밀리리터;총량 : 100밀리리터|성분명 : 클로르헥시딘글루콘산염 액|분량 : 10|단위 : 밀리리터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염(으)로서 2 그램;총량 : 100밀리리터|성분명 : 에탄올(95)|분량 : 75|단위 : 밀리리터|규격 : KP|성분정보 : 에탄올(으)로서 72 밀리리터', '함량_총량기준': '100-제 1처방(무색)/100-제 2처방(붉은색)/100-제 3처방(파란색)', '수집URL': 'https://drug.hospitalk.net/item/201903835', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201903835', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200801347', 'ITEM_NAME': '구미히비크린에이액(글루콘산클로르헥시딘액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '글루콘산클로르헥시딘액', 'ENTP_NAME': '구미제약(주)', 'CHART': '반투명한 주홍색의 향긋한 냄새가 나는 점성액제', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806804001906,8806804001913,8806804001920', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M243030]글루콘산클로르헥시딘액|[M243030]글루콘산클로르헥시딘액', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 글루콘산클로르헥시딘액|분량 : 20.0|단위 : 밀리리터|규격 : KP|성분정보 : 글루콘산클로르헥시딘으로서4그램;총량 : 100밀리리터|성분명 : 글루콘산클로르헥시딘액|분량 : 20.0|단위 : 밀리리터|규격 : KP|성분정보 : 글루콘산클로르헥시딘으로서4그램', '함량_총량기준': '100/100', '수집URL': 'https://drug.hospitalk.net/item/200801347', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200801347', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200801686', 'ITEM_NAME': '구바파정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '의이인엑스(13→1);L-시스테인;d-비오틴1%;니코틴산아미드;아스코르브산97%과립;피리독신염산염;리보플라빈부티레이트', 'ENTP_NAME': '(주)아이월드제약', 'CHART': '분홍색의 원형 필름코팅정', 'CHANGE_DATE': '2016-06-09', 'BAR_CODE': '8806696030008,8806696030015,8806696030022', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M207452]의이인엑스(13→1)|[M204437]L-시스테인|[M253623]d-비오틴1%|[M040064]니코틴산아미드|[M227509]아스코르브산97%과립|[M204304]피리독신염산염|[M222995]리보플라빈부티레이트', '함량_원료성분원문': '총량 : 1정(350mg)중|성분명 : 리보플라빈부티레이트|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(350mg)중|성분명 : 피리독신염산염|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(350mg)중|성분명 : 아스코르브산97%과립|분량 : 25.77|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : 아스코르브산으로서 25mg;총량 : 1정(350mg)중|성분명 : 니코틴산아미드|분량 : 15|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(350mg)중|성분명 : d-비오틴1%|분량 : 2.5|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : 비오틴으로서 25ug;총량 : 1정(350mg)중|성분명 : L-시스테인|분량 : 15|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1정(350mg)중|성분명 : 의이인엑스(13→1)|분량 : 50|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1정(350mg)중', '수집URL': 'https://drug.hospitalk.net/item/200801686', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200801686', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200809204', 'ITEM_NAME': '구아내정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '의이인엑스(13→1);비오틴;판토텐산칼슘;니코틴산아미드;L-시스테인;제피아스코르브산;피리독신염산염;리보플라빈부티레이트', 'ENTP_NAME': '(주)한풍제약', 'CHART': '적갈색의 장방형 필름코팅정제', 'CHANGE_DATE': '2023-04-12', 'BAR_CODE': '8806581043601,8806581043618,8806581043625,8806581043632,8806581043649', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M207452]의이인엑스(13→1)|[M050704]비오틴|[M244748]판토텐산칼슘|[M040064]니코틴산아미드|[M204437]L-시스테인|[M236913]제피아스코르브산|[M204304]피리독신염산염|[M222995]리보플라빈부티레이트', '함량_원료성분원문': '총량 : 1정(600mg) 중|성분명 : 리보플라빈부티레이트|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(600mg) 중|성분명 : 피리독신염산염|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(600mg) 중|성분명 : 제피아스코르브산|분량 : 52.1|단위 : 밀리그램|규격 : 별규|성분정보 : 아스코르브산으로서 50mg;총량 : 1정(600mg) 중|성분명 : L-시스테인|분량 : 30|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1정(600mg) 중|성분명 : 니코틴산아미드|분량 : 25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(600mg) 중|성분명 : 판토텐산칼슘|분량 : 15|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(600mg) 중|성분명 : 비오틴|분량 : 25|단위 : 마이크로그램|규격 : USP|성분정보 : ;총량 : 1정(600mg) 중|성분명 : 의이인엑스(13→1)|분량 : 55|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 :', '함량_총량기준': '1정(600mg) 중', '수집URL': 'https://drug.hospitalk.net/item/200809204', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200809204', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200102905', 'ITEM_NAME': '구주로라타딘정10밀리그람(수출명:로히스타정)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '로라타딘', 'ENTP_NAME': '구주제약(주)', 'CHART': '흰색의 타원형 정제', 'CHANGE_DATE': '2019-09-18', 'BAR_CODE': '8806698001006,8806698001013,8806698001020,8806698001037', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M082724]로라타딘', '함량_원료성분원문': '총량 : 1정100밀리그램|성분명 : 로라타딘|분량 : 10.0|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1100', '수집URL': 'https://drug.hospitalk.net/item/200102905', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200102905', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199803123', 'ITEM_NAME': '구청껌정(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '플루오르화나트륨;염화세칠피리디늄', 'ENTP_NAME': '(주)새한제약', 'CHART': '이 약은 녹색의 사각형 츄잉껌 정제이다', 'CHANGE_DATE': '2014-12-03', 'BAR_CODE': '8806513000108,8806513000115', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223322]플루오르화나트륨|[M230954]염화세칠피리디늄', '함량_원료성분원문': '총량 : 츄잉껌 1정(1.5g) 중|성분명 : 염화세칠피리디늄|분량 : 2.0|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 츄잉껌 1정(1.5g) 중|성분명 : 플루오르화나트륨|분량 : 0.5|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '츄잉껌 1정(1.5g) 중', '수집URL': 'https://drug.hospitalk.net/item/199803123', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199803123', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199700530', 'ITEM_NAME': '국제아시클로버크림', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아시클로버', 'ENTP_NAME': '국제약품(주)', 'CHART': '전질이 고른 흰색의 크림제', 'CHANGE_DATE': '2022-11-09', 'BAR_CODE': '8806437005807,8806437005814,8806437005821,8806437005838,8806437005845', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081569]아시클로버', '함량_원료성분원문': '총량 : 1그램|성분명 : 아시클로버|분량 : 50|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/199700530', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199700530', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202502694', 'ITEM_NAME': '국제은행엽건조엑스정120밀리그램', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은행엽 건조엑스', 'ENTP_NAME': '국제약품(주)', 'CHART': '녹색의 원형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '미기재', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M273892]은행엽 건조엑스', '함량_원료성분원문': '총량 : 1정295.6밀리그램|성분명 : 은행엽 건조엑스|분량 : 120.0|단위 : 밀리그램|규격 : 생규|성분정보 : 총깅코플라본배당체(으)로서 28.8 밀리그램', '함량_총량기준': '1295.6', '수집URL': 'https://drug.hospitalk.net/item/202502694', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202502694', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202001598', 'ITEM_NAME': '굿라인정(방풍통성산)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '작약;천궁;연교;박하;방풍;마황;대황;망초;활석;감초;백출;형개;치자;생강;석고;황금;길경;당귀', 'ENTP_NAME': '한국신텍스제약(주)', 'CHART': '갈색의 정제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806230069501,8806230069518,8806230069525,8806230069532,8806230069549,8806230069556', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040523]작약|[M040550]천궁|[M051105]연교|[M040198]박하|[M040205]방풍|[M040135]마황|[M040073]대황|[M088654]망초|[M071732]활석|[M040006]감초|[M040214]백출|[M051936]형개|[M040564]치자|[M050752]생강|[M040279]석고|[M040789]황금|[M040048]길경|[M040070]당귀', '함량_원료성분원문': '총량 : 1정400밀리그램|성분명 : 당귀|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정400밀리그램|성분명 : 길경|분량 : 223.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정400밀리그램|성분명 : 황금|분량 : 223.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정400밀리그램|성분명 : 석고|분량 : 333.3|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1정400밀리그램|성분명 : 생강|분량 : 133.3|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1정400밀리그램|성분명 : 치자|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정400밀리그램|성분명 : 형개|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정400밀리그램|성분명 : 백출|분량 : 223.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정400밀리그램|성분명 : 감초|분량 : 223.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정400밀리그램|성분명 : 활석|분량 : 556.7|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1정400밀리그램|성분명 : 작약|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정400밀리그램|성분명 : 천궁|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정400밀리그램|성분명 : 연교|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정400밀리그램|성분명 : 박하|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정400밀리그램|성분명 : 방풍|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정400밀리그램|성분명 : 마황|분량 : 133.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정400밀리그램|성분명 : 대황|분량 : 166.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정400밀리그램|성분명 : 망초|분량 : 166.7|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1400', '수집URL': 'https://drug.hospitalk.net/item/202001598', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202001598', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201206827', 'ITEM_NAME': '굿모닝에스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '지실엑스산;생강엑스산;육계;작약엑스산;감초엑스산;차전자피;센나열매;대황', 'ENTP_NAME': '(주)한풍제약', 'CHART': '갈색의 과립제', 'CHANGE_DATE': '2025-04-24', 'BAR_CODE': '8806581050104,8806581050111,8806581050128,8806581050135', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089604]지실엑스산|[M089512]생강엑스산|[M050036]육계|[M090093]작약엑스산|[M082727]감초엑스산|[M081198]차전자피|[M050805]센나열매|[M040073]대황', '함량_원료성분원문': '총량 : 1포(4.80g)중|성분명 : 대황|분량 : 1000|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(4.80g)중|성분명 : 센나열매|분량 : 500|단위 : 밀리그램|규격 : BP|성분정보 : ;총량 : 1포(4.80g)중|성분명 : 차전자피|분량 : 2000|단위 : 밀리그램|규격 : BP|성분정보 : ;총량 : 1포(4.80g)중|성분명 : 감초엑스산|분량 : 300|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포(4.80g)중|성분명 : 작약엑스산|분량 : 300|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포(4.80g)중|성분명 : 육계|분량 : 80|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(4.80g)중|성분명 : 생강엑스산|분량 : 20|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포(4.80g)중|성분명 : 지실엑스산|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1포(4.80g)중', '수집URL': 'https://drug.hospitalk.net/item/201206827', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201206827', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201708002', 'ITEM_NAME': '굿모닝에이스정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '작약엑스산;감초엑스산;센나열매;비사코딜;도큐세이트나트륨', 'ENTP_NAME': '(주)한풍제약', 'CHART': '녹색의 장용성 필름코팅정', 'CHANGE_DATE': '2022-10-20', 'BAR_CODE': '8806581060301,8806581060318,8806581060325', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M090093]작약엑스산|[M082727]감초엑스산|[M050805]센나열매|[M050687]비사코딜|[M081950]도큐세이트나트륨', '함량_원료성분원문': '총량 : 1정350밀리그램|성분명 : 도큐세이트나트륨|분량 : 10.0|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1정350밀리그램|성분명 : 비사코딜|분량 : 3.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정350밀리그램|성분명 : 센나열매|분량 : 75.0|단위 : 밀리그램|규격 : BP|성분정보 : ;총량 : 1정350밀리그램|성분명 : 감초엑스산|분량 : 75.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1정350밀리그램|성분명 : 작약엑스산|분량 : 50.0|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1350', '수집URL': 'https://drug.hospitalk.net/item/201708002', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201708002', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200100074', 'ITEM_NAME': '굿모닝에프과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '생강엑스산;육계 엑스산;대추엑스산;작약엑스산;감초엑스산;차전자피;센나열매;대황', 'ENTP_NAME': '(주)한풍제약', 'CHART': '갈색의 과립', 'CHANGE_DATE': '2024-05-08', 'BAR_CODE': '8806581002103,8806581002110,8806581002127,8806581002134,8806581002141,8806581002158', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M089512]생강엑스산|[M110942]육계 엑스산|[M089515]대추엑스산|[M090093]작약엑스산|[M082727]감초엑스산|[M081198]차전자피|[M050805]센나열매|[M040073]대황', '함량_원료성분원문': '총량 : 1회4.5그램|성분명 : 대황|분량 : 1.0|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회4.5그램|성분명 : 센나열매|분량 : 0.5|단위 : 그램|규격 : BP|성분정보 : ;총량 : 1회4.5그램|성분명 : 차전자피|분량 : 2.0|단위 : 그램|규격 : BP|성분정보 : ;총량 : 1회4.5그램|성분명 : 감초엑스산|분량 : 0.25|단위 : 그램|규격 : 별규|성분정보 : ;총량 : 1회4.5그램|성분명 : 작약엑스산|분량 : 0.25|단위 : 그램|규격 : 별규|성분정보 : ;총량 : 1회4.5그램|성분명 : 대추엑스산|분량 : 0.25|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회4.5그램|성분명 : 육계 엑스산|분량 : 0.0415|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1회4.5그램|성분명 : 생강엑스산|분량 : 0.0275|단위 : 그램|규격 : 생규|성분정보 :', '함량_총량기준': '14.5', '수집URL': 'https://drug.hospitalk.net/item/200100074', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200100074', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200900682', 'ITEM_NAME': '굿스펜연질캡슐(덱시부프로펜)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '덱시부프로펜', 'ENTP_NAME': '광동제약(주)', 'CHART': '[내수용] 무색 내지 미색의 투명한 액상 내용물을 함유한 투명한 장방형 연질캡슐 [수출용] 미황색의 투명한 유상내용물이 든 주황색의 투명한 타원형 연질캡슐', 'CHANGE_DATE': '2026-01-02', 'BAR_CODE': '8806418038909,8806418038916', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M092057]덱시부프로펜|[M092057]덱시부프로펜', '함량_원료성분원문': '총량 : [내수용: 1캡슐(1,085mg)중] [수출용: 1캡슐(800mg)중]|성분명 : 덱시부프로펜|분량 : 300|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : [내수용: 1캡슐(1,085mg)중] [수출용: 1캡슐(800mg)중]|성분명 : 덱시부프로펜|분량 : 300|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '[내수용: 1캡슐(1,085mg)중] [수출용: 1캡슐(800mg)중]-내수용/[내수용: 1캡슐(1,085mg)중] [수출용: 1캡슐(800mg)중]-수출용', '수집URL': 'https://drug.hospitalk.net/item/200900682', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200900682', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202106656', 'ITEM_NAME': '굿포미정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '레보노르게스트렐;에티닐에스트라디올', 'ENTP_NAME': '조아제약(주)', 'CHART': '분홍색의 원형 필름코팅정', 'CHANGE_DATE': '2026-05-08', 'BAR_CODE': '8806446043203,8806446043210', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M095487]레보노르게스트렐|[M223147]에티닐에스트라디올', '함량_원료성분원문': '총량 : 1정80밀리그램|성분명 : 레보노르게스트렐|분량 : 0.1|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1정80밀리그램|성분명 : 에티닐에스트라디올|분량 : 0.02|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '180', '수집URL': 'https://drug.hospitalk.net/item/202106656', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202106656', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '197900017', 'ITEM_NAME': '귀비론과립(가미귀비탕엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '가미귀비탕연조엑스', 'ENTP_NAME': '(주)한풍제약', 'CHART': '갈색의 과립제', 'CHANGE_DATE': '2023-04-17', 'BAR_CODE': '8806581002301,8806581002318,8806581002325', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M243810]가미귀비탕연조엑스', '함량_원료성분원문': '총량 : 1회4그램|성분명 : 가미귀비탕연조엑스|분량 : 3440|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '14', '수집URL': 'https://drug.hospitalk.net/item/197900017', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=197900017', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202302739', 'ITEM_NAME': '그날엔노즈에이연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '슈도에페드린염산염;클로르페니라민말레산염;아세트아미노펜', 'ENTP_NAME': '경동제약(주)', 'CHART': '미황색 내지 연한 적색의 투명한 내용물을 함유한 적색의 투명한 타원형 연질캡슐제', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806481049604,8806481049611', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M203364]슈도에페드린염산염|[M223211]클로르페니라민말레산염|[M040353]아세트아미노펜', '함량_원료성분원문': '총량 : 1캡슐1005밀리그램|성분명 : 아세트아미노펜|분량 : 200|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐1005밀리그램|성분명 : 클로르페니라민말레산염|분량 : 1.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐1005밀리그램|성분명 : 슈도에페드린염산염|분량 : 15|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '11005', '수집URL': 'https://drug.hospitalk.net/item/202302739', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202302739', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201705221', 'ITEM_NAME': '그날엔노즈플러스연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아세트아미노펜;브롬페니라민말레산염;슈도에페드린염산염', 'ENTP_NAME': '경동제약(주)', 'CHART': '연노랑 내지 연한 청색의 투명한 내용물을 함유한 청색의 투명한 장방형 연질캡슐', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806481039605,8806481039612', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040353]아세트아미노펜|[M247022]브롬페니라민말레산염|[M203364]슈도에페드린염산염', '함량_원료성분원문': '총량 : 1캡슐(1,300 밀리그램) 중|성분명 : 아세트아미노펜|분량 : 200.000|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1캡슐(1,300 밀리그램) 중|성분명 : 브롬페니라민말레산염|분량 : 2.660|단위 : 밀리그램|규격 : BP|성분정보 : ;총량 : 1캡슐(1,300 밀리그램) 중|성분명 : 슈도에페드린염산염|분량 : 15.000|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1캡슐(1,300 밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201705221', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201705221', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202107347', 'ITEM_NAME': '그날엔더블유연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '리보플라빈;산화마그네슘;파마브롬;이부프로펜', 'ENTP_NAME': '경동제약(주)', 'CHART': '일부분 황색의 유상내용물, 일부분 무색의 투명한 액을 함유한 주황색의 타원형 연질캡슐', 'CHANGE_DATE': '2025-10-10', 'BAR_CODE': '8806481047402,8806481047419', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040133]리보플라빈|[M040262]산화마그네슘|[M082487]파마브롬|[M051259]이부프로펜', '함량_원료성분원문': '총량 : 1캡슐1010밀리그램|성분명 : 이부프로펜|분량 : 200|단위 : 밀리그램|규격 : BP|성분정보 : ;총량 : 1캡슐1010밀리그램|성분명 : 파마브롬|분량 : 25|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1캡슐1010밀리그램|성분명 : 산화마그네슘|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : 마그네슘(으)로서 30.16 밀리그램;총량 : 1캡슐1010밀리그램|성분명 : 리보플라빈|분량 : 2|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '11010', '수집URL': 'https://drug.hospitalk.net/item/202107347', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202107347', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201903015', 'ITEM_NAME': '그날엔덱스연질캡슐(덱시부프로펜)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '덱시부프로펜', 'ENTP_NAME': '경동제약(주)', 'CHART': '무색의 액상 내용물을 함유한 투명한 타원형 연질캡슐', 'CHANGE_DATE': '2026-01-02', 'BAR_CODE': '8806481043107,8806481043114', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M254719]덱시부프로펜', '함량_원료성분원문': '총량 : 1캡슐785밀리그램|성분명 : 덱시부프로펜|분량 : 300.000|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1785', '수집URL': 'https://drug.hospitalk.net/item/201903015', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201903015', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201800891', 'ITEM_NAME': '그날엔딥24플라스타(디클로페낙나트륨)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '디클로페낙나트륨', 'ENTP_NAME': '경동제약(주)', 'CHART': '무색투명 내지 미황색의 점착성 물질을 지지체에 도포하고(바르고) 고체면에 고체피복물을 덮은 첩부제이다.', 'CHANGE_DATE': '2024-12-12', 'BAR_CODE': '8806481040403,8806481040410,8806481040427', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050288]디클로페낙나트륨|[M050288]디클로페낙나트륨', '함량_원료성분원문': '총량 : 1매 (7cm X 10.1cm, 70cm², 2.41g) 중|성분명 : 디클로페낙나트륨|분량 : 15|단위 : 밀리그램|규격 : BP|성분정보 : ;총량 : 1매 (7cm X 10.1cm, 70cm², 2.41g) 중|성분명 : 디클로페낙나트륨|분량 : 15|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '1매 (7cm X 10.1cm, 70cm², 2.41g) 중-C-type/1매 (7cm X 10.1cm, 70cm², 2.41g) 중-H-type', '수집URL': 'https://drug.hospitalk.net/item/201800891', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201800891', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202302140', 'ITEM_NAME': '그날엔에이스연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '리보플라빈;아세트아미노펜', 'ENTP_NAME': '경동제약(주)', 'CHART': '노랑 내지 주황색의 내용물을 함유한 적갈색의 타원형 연질캡슐', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806481049307,8806481049314', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040133]리보플라빈|[M040353]아세트아미노펜', '함량_원료성분원문': '총량 : 1캡슐1050밀리그램|성분명 : 아세트아미노펜|분량 : 400|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐1050밀리그램|성분명 : 리보플라빈|분량 : 4|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '11050', '수집URL': 'https://drug.hospitalk.net/item/202302140', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202302140', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200902301', 'ITEM_NAME': '그날엔정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '카페인무수물;알릴이소프로필아세틸우레아;이부프로펜', 'ENTP_NAME': '경동제약(주)', 'CHART': '상, 하층은 백색 내지 유백색이고 중간층은 적색 내지 연적색인 원형 필름코팅 삼중정제이며, 상,하층에 적색반점이 있을 수 있다.', 'CHANGE_DATE': '2024-07-15', 'BAR_CODE': '8806481026001,8806481026018,8806481026025,8806481026032', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223183]카페인무수물|[M255360]알릴이소프로필아세틸우레아|[M051259]이부프로펜', '함량_원료성분원문': '총량 : 이 약 1정(215밀리그램) 중|성분명 : 이부프로펜|분량 : 75.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1정(215밀리그램) 중|성분명 : 알릴이소프로필아세틸우레아|분량 : 30.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1정(215밀리그램) 중|성분명 : 카페인무수물|분량 : 40.0|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '이 약 1정(215밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200902301', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200902301', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202302948', 'ITEM_NAME': '그날엔코프에이연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아세트아미노펜;dl-메틸에페드린염산염;덱스트로메토르판브롬화수소산염수화물;구아이페네신', 'ENTP_NAME': '경동제약(주)', 'CHART': '미황색 내지 연한 청색의 투명한 내용물을 함유한 청색의 투명한 타원형 연질캡슐제', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806481049703,8806481049710', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040353]아세트아미노펜|[M204422]dl-메틸에페드린염산염|[M222957]덱스트로메토르판브롬화수소산염수화물|[M050058]구아이페네신', '함량_원료성분원문': '총량 : 1캡슐1085밀리그램|성분명 : 아세트아미노펜|분량 : 200|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐1085밀리그램|성분명 : dl-메틸에페드린염산염|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐1085밀리그램|성분명 : 덱스트로메토르판브롬화수소산염수화물|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐1085밀리그램|성분명 : 구아이페네신|분량 : 40|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '11085', '수집URL': 'https://drug.hospitalk.net/item/202302948', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202302948', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201705220', 'ITEM_NAME': '그날엔코프플러스연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로페라스틴염산염;노스카핀염산염수화물;아세트아미노펜', 'ENTP_NAME': '경동제약(주)', 'CHART': '연노랑 내지 연한 녹색의 투명한 내용물을 함유한 녹색의 투명한 장방형 연질캡슐', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806481039407,8806481039414', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M222890]클로페라스틴염산염|[M223470]노스카핀염산염수화물|[M040353]아세트아미노펜', '함량_원료성분원문': '총량 : 1캡슐(1,160 밀리그램) 중|성분명 : 아세트아미노펜|분량 : 200.00|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1캡슐(1,160 밀리그램) 중|성분명 : 노스카핀염산염수화물|분량 : 5.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,160 밀리그램) 중|성분명 : 클로페라스틴염산염|분량 : 8.00|단위 : 밀리그램|규격 : JP|성분정보 :', '함량_총량기준': '1캡슐(1,160 밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201705220', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201705220', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202302949', 'ITEM_NAME': '그날엔콜드에이연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '구아이페네신;덱스트로메토르판브롬화수소산염수화물;슈도에페드린염산염;dl-메틸에페드린염산염;클로르페니라민말레산염;아세트아미노펜', 'ENTP_NAME': '경동제약(주)', 'CHART': '미황색의 투명한 내용물을 함유한 노란색의 투명한 타원형 연질캡슐제', 'CHANGE_DATE': '2026-07-14', 'BAR_CODE': '8806481049802,8806481049819', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050058]구아이페네신|[M222957]덱스트로메토르판브롬화수소산염수화물|[M203364]슈도에페드린염산염|[M204422]dl-메틸에페드린염산염|[M223211]클로르페니라민말레산염|[M040353]아세트아미노펜', '함량_원료성분원문': '총량 : 1캡슐1075밀리그램|성분명 : 아세트아미노펜|분량 : 200|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐1075밀리그램|성분명 : 클로르페니라민말레산염|분량 : 1.25|단위 : 밀리그램|규격 : EP|성분정보 : ;총량 : 1캡슐1075밀리그램|성분명 : dl-메틸에페드린염산염|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐1075밀리그램|성분명 : 슈도에페드린염산염|분량 : 15|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1캡슐1075밀리그램|성분명 : 덱스트로메토르판브롬화수소산염수화물|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐1075밀리그램|성분명 : 구아이페네신|분량 : 41.6|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '11075', '수집URL': 'https://drug.hospitalk.net/item/202302949', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202302949', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201705219', 'ITEM_NAME': '그날엔콜드플러스연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '구아이페네신;클로페라스틴염산염;브롬페니라민말레산염;슈도에페드린염산염;아세트아미노펜', 'ENTP_NAME': '경동제약(주)', 'CHART': '연노랑의 투명한 내용물을 함유한 노란색의 투명한 장방형 연질캡슐', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806481039506,8806481039513', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050058]구아이페네신|[M222890]클로페라스틴염산염|[M247022]브롬페니라민말레산염|[M203364]슈도에페드린염산염|[M040353]아세트아미노펜', '함량_원료성분원문': '총량 : 1캡슐(1,300 밀리그램) 중|성분명 : 아세트아미노펜|분량 : 200.000|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1캡슐(1,300 밀리그램) 중|성분명 : 슈도에페드린염산염|분량 : 15.000|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1캡슐(1,300 밀리그램) 중|성분명 : 브롬페니라민말레산염|분량 : 2.660|단위 : 밀리그램|규격 : BP|성분정보 : ;총량 : 1캡슐(1,300 밀리그램) 중|성분명 : 클로페라스틴염산염|분량 : 8.000|단위 : 밀리그램|규격 : JP|성분정보 : ;총량 : 1캡슐(1,300 밀리그램) 중|성분명 : 구아이페네신|분량 : 41.600|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1캡슐(1,300 밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201705219', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201705219', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200906330', 'ITEM_NAME': '그날엔큐정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '산화마그네슘;카페인무수물;알릴이소프로필아세틸우레아;이부프로펜', 'ENTP_NAME': '경동제약(주)', 'CHART': '흰색의 원형 필름코팅정', 'CHANGE_DATE': '2024-07-15', 'BAR_CODE': '8806481027602,8806481027619,8806481027626,8806481027633', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040262]산화마그네슘|[M223183]카페인무수물|[M255360]알릴이소프로필아세틸우레아|[M051259]이부프로펜', '함량_원료성분원문': '총량 : 이 약 1정(324.82밀리그램) 중|성분명 : 이부프로펜|분량 : 75.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1정(324.82밀리그램) 중|성분명 : 알릴이소프로필아세틸우레아|분량 : 30.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1정(324.82밀리그램) 중|성분명 : 카페인무수물|분량 : 40.0|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 이 약 1정(324.82밀리그램) 중|성분명 : 산화마그네슘|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 1정(324.82밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200906330', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200906330', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200702972', 'ITEM_NAME': '그라보스정(은행엽건조엑스) (수출용)(수출명 : GRABOS Tablet)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은행엽건조엑스', 'ENTP_NAME': '(주)넥스팜코리아', 'CHART': '녹색의 원형 필름코팅정', 'CHANGE_DATE': '2022-08-19', 'BAR_CODE': '8806625019401,8806625019418', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M088948]은행엽건조엑스', '함량_원료성분원문': '총량 : 1정 (232.0mg)중|성분명 : 은행엽건조엑스|분량 : 80.0|단위 : 밀리그램|규격 : 생규|성분정보 : 총 깅코플라본배당체로서 19.2mg', '함량_총량기준': '1정 (232.0mg)중', '수집URL': 'https://drug.hospitalk.net/item/200702972', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200702972', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201802183', 'ITEM_NAME': '그라톤정(은행엽건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은행엽 건조엑스', 'ENTP_NAME': '(주)서울제약', 'CHART': '연녹색의 장방형 필름코팅정', 'CHANGE_DATE': '2021-11-11', 'BAR_CODE': '8800524007507,8800524007514,8800524007521,8800524007538,8800524007545,8806529045803,8806529045810,8806529045827', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M273892]은행엽 건조엑스', '함량_원료성분원문': '총량 : 1정310.0밀리그램|성분명 : 은행엽 건조엑스|분량 : 40.0|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1310.0', '수집URL': 'https://drug.hospitalk.net/item/201802183', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201802183', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202400825', 'ITEM_NAME': '그라톤정240밀리그램(은행엽건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은행엽 건조엑스', 'ENTP_NAME': '(주)서울제약', 'CHART': '녹색의 장방형 필름코팅정제', 'CHANGE_DATE': '2025-06-10', 'BAR_CODE': '8806529047104,8806529047111,8806529047128', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M273892]은행엽 건조엑스', '함량_원료성분원문': '총량 : 1정630밀리그램|성분명 : 은행엽 건조엑스|분량 : 240|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1630', '수집URL': 'https://drug.hospitalk.net/item/202400825', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202400825', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198800444', 'ITEM_NAME': '그랑페롤연질캡슐1000아이유(비타민이프리퍼레이션)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '비타민이프리퍼레이션', 'ENTP_NAME': '(주)유한양행', 'CHART': '황색-황갈색의 유상(기름상태)액이 충진(충전)된 미황색(연노랑)의 장방형 연질캡슐제.', 'CHANGE_DATE': '2021-07-23', 'BAR_CODE': '8806421000405,8806421000412', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256359]비타민이프리퍼레이션', '함량_원료성분원문': '총량 : 1캡슐(1,210mg) 중|성분명 : 비타민이프리퍼레이션|분량 : 1,000.00|단위 : 아이.유|규격 : 별첨규격(전과동)|성분정보 : 디-알파-토코페롤로서 671.1mg', '함량_총량기준': '1캡슐(1,210mg) 중', '수집URL': 'https://drug.hospitalk.net/item/198800444', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198800444', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198700431', 'ITEM_NAME': '그랑페롤연질캡슐400아이유(비타민이프리퍼레이션)(군납명:토코페롤연질캡슐400아이유100캡슐)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '비타민이프리퍼레이션', 'ENTP_NAME': '(주)유한양행', 'CHART': '황색-황갈색의 유상(기름상태)액이 충진(충전)된 미황색(연노랑) 타원형의 연질캡슐제', 'CHANGE_DATE': '2021-07-23', 'BAR_CODE': '8806421000603,8806421000610', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256359]비타민이프리퍼레이션', '함량_원료성분원문': '총량 : 1캡슐(811밀리그램)중|성분명 : 비타민이프리퍼레이션|분량 : 400.00|단위 : 아이.유|규격 : 별규|성분정보 : 디-알파토코페롤로서 268.50mg', '함량_총량기준': '1캡슐(811밀리그램)중', '수집URL': 'https://drug.hospitalk.net/item/198700431', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198700431', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199502365', 'ITEM_NAME': '그루타제정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '디메티콘;우담즙건조엑스;셀룰라제;판크레아틴', 'ENTP_NAME': '지엘팜텍(주)', 'CHART': '장방형의 장용피를 한 연녹색의 필름코팅정', 'CHANGE_DATE': '2025-06-11', 'BAR_CODE': '8806242003708,8806242003715,8806497000408,8806497000415,8806497000422,8806497000439,8806497000446', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M227778]디메티콘|[M268886]우담즙건조엑스|[M100297]셀룰라제|[M040678]판크레아틴', '함량_원료성분원문': '총량 : 1정509.0밀리그램|성분명 : 판크레아틴|분량 : 175.0|단위 : 밀리그램|규격 : USP|성분정보 : 전분당화력2961.81단위/일, 단백소화력 39643.31단위/일, 지방소화력 1331.36단위/일;총량 : 1정509.0밀리그램|성분명 : 셀룰라제|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : 섬유소당화력 62.39단위/일;총량 : 1정509.0밀리그램|성분명 : 우담즙건조엑스|분량 : 25.0|단위 : 밀리그램|규격 : 생규|성분정보 : 콜린산으로서 11.25밀리그램;총량 : 1정509.0밀리그램|성분명 : 디메티콘|분량 : 25.0|단위 : 밀리그램|규격 : NF|성분정보 :', '함량_총량기준': '1509.0', '수집URL': 'https://drug.hospitalk.net/item/199502365', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199502365', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200202148', 'ITEM_NAME': '그리펜-에스정(덱시부프로펜)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '덱시부프로펜', 'ENTP_NAME': '신일제약(주)', 'CHART': '분홍색의 원형 필름코팅정', 'CHANGE_DATE': '2026-01-02', 'BAR_CODE': '8806538000602,8806538000619,8806538000626', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M092057]덱시부프로펜', '함량_원료성분원문': '총량 : 1정(481.0mg) 중|성분명 : 덱시부프로펜|분량 : 300.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정(481.0mg) 중', '수집URL': 'https://drug.hospitalk.net/item/200202148', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200202148', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199603311', 'ITEM_NAME': '그린관장약(농글리세린)(수출명:FIT-APO)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '농글리세린', 'ENTP_NAME': '(주)그린제약', 'CHART': '무색 투명한 액체', 'CHANGE_DATE': '2014-06-09', 'BAR_CODE': '8806483000405,8806483000412,8806483000429,8806483000436,8806483000443', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040044]농글리세린', '함량_원료성분원문': '총량 : 이 약 100mL 중|성분명 : 농글리세린|분량 : 50|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 100mL 중', '수집URL': 'https://drug.hospitalk.net/item/199603311', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199603311', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201802836', 'ITEM_NAME': '그린나잘스프레이모이스쳐액(옥시메타졸린염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '옥시메타졸린염산염', 'ENTP_NAME': '(주)그린제약', 'CHART': '무색 또는 미황색의 맑은 액', 'CHANGE_DATE': '2025-12-03', 'BAR_CODE': '8806483011401,8806483011418,8806483011425', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223162]옥시메타졸린염산염', '함량_원료성분원문': '총량 : 이 약 100mL 중|성분명 : 옥시메타졸린염산염|분량 : 0.05|단위 : 그램|규격 : USP|성분정보 :', '함량_총량기준': '이 약 100mL 중', '수집URL': 'https://drug.hospitalk.net/item/201802836', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201802836', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202602184', 'ITEM_NAME': '그린노즈스트롱연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르페니라민말레산염;슈도에페드린염산염;벨라돈나총알칼로이드', 'ENTP_NAME': '(주)녹십자', 'CHART': '미황색의 투명한 내용물을 함유한 미황색의 투명한 타원형 연질캡슐', 'CHANGE_DATE': '2026-09-18', 'BAR_CODE': '8806436073807,8806436073814', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223211]클로르페니라민말레산염|[M203364]슈도에페드린염산염|[M086528]벨라돈나총알칼로이드', '함량_원료성분원문': '총량 : 1캡슐335밀리그램|성분명 : 클로르페니라민말레산염|분량 : 4|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐335밀리그램|성분명 : 슈도에페드린염산염|분량 : 25|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1캡슐335밀리그램|성분명 : 벨라돈나총알칼로이드|분량 : 0.2|단위 : 밀리그램|규격 : JP|성분정보 : 총 알칼로이드(으)로서 0.2 밀리그램', '함량_총량기준': '1335', '수집URL': 'https://drug.hospitalk.net/item/202602184', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202602184', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201603449', 'ITEM_NAME': '그린노즈에스시럽', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르페니라민말레산염;슈도에페드린염산염', 'ENTP_NAME': '(주)녹십자', 'CHART': '갈색유리병에 담긴 무색의 딸기향이 있는 시럽제', 'CHANGE_DATE': '2025-07-30', 'BAR_CODE': '8806436052109,8806436052116', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223211]클로르페니라민말레산염|[M203364]슈도에페드린염산염', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 클로르페니라민말레산염|분량 : 20|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 100밀리리터|성분명 : 슈도에페드린염산염|분량 : 300|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/201603449', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201603449', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200902769', 'ITEM_NAME': '그린노즈에스캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '벨라돈나총알칼로이드;페닐레프린염산염;클로르페니라민말레산염', 'ENTP_NAME': '맥널티제약(주)', 'CHART': '흰색, 적색 및 노란색의 구형과립이 들어있는 상부 녹색투명, 하부 무색투명의 경질캡슐', 'CHANGE_DATE': '2020-11-26', 'BAR_CODE': '8806415014005,8806415014012', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M086528]벨라돈나총알칼로이드|[M222724]페닐레프린염산염|[M223211]클로르페니라민말레산염', '함량_원료성분원문': '총량 : 1캡슐284.4밀리그램|성분명 : 클로르페니라민말레산염|분량 : 3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐284.4밀리그램|성분명 : 페닐레프린염산염|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐284.4밀리그램|성분명 : 벨라돈나총알칼로이드|분량 : 0.133|단위 : 밀리그램|규격 : JP|성분정보 : 히요스시아민으로서 0.127mg', '함량_총량기준': '1284.4', '수집URL': 'https://drug.hospitalk.net/item/200902769', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200902769', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202401758', 'ITEM_NAME': '그린노즈플러스연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '벨라돈나총알칼로이드;카페인무수물;클로르페니라민말레산염', 'ENTP_NAME': '(주)녹십자', 'CHART': '흰색의 내용물을 함유한 연두색의 타원형 연질캡슐', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806436067202,8806436067219', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M086528]벨라돈나총알칼로이드|[M223183]카페인무수물|[M223211]클로르페니라민말레산염', '함량_원료성분원문': '총량 : 1캡슐330.00밀리그램|성분명 : 클로르페니라민말레산염|분량 : 4.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐330.00밀리그램|성분명 : 카페인무수물|분량 : 25.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐330.00밀리그램|성분명 : 벨라돈나총알칼로이드|분량 : 0.20|단위 : 밀리그램|규격 : JP|성분정보 : 총알칼로이드(으)로서 0.20 밀리그램', '함량_총량기준': '1330.00', '수집URL': 'https://drug.hospitalk.net/item/202401758', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202401758', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200710524', 'ITEM_NAME': '그린라인경질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '다엽 가루;오르소시폰 가루', 'ENTP_NAME': '미래바이오제약(주)', 'CHART': '갈색의 가루가 충전된 상부 암녹색, 하부 미황색의 경질캡슐', 'CHANGE_DATE': '2023-12-11', 'BAR_CODE': '8806575000405,8806575000412,8806575000429', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M112209]다엽 가루|[M111600]오르소시폰 가루', '함량_원료성분원문': '총량 : 1캡슐(505밀리그램) 중|성분명 : 다엽 가루|분량 : 250|단위 : 밀리그램|규격 : 생규|성분정보 : 카페인(으)로서 5 밀리그램;총량 : 1캡슐(505밀리그램) 중|성분명 : 오르소시폰 가루|분량 : 150|단위 : 밀리그램|규격 : 생규|성분정보 : 시넨세틴(으)로서 67.5 마이크로그램', '함량_총량기준': '1캡슐(505밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200710524', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200710524', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200001205', 'ITEM_NAME': '그린미캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '다엽가루;오르소시폰가루', 'ENTP_NAME': '정우신약(주)', 'CHART': '녹색의 분말이 충진된 상-하 초록색의 캡슐제', 'CHANGE_DATE': '2018-01-21', 'BAR_CODE': '8806452002003,8806452002010,8806452002027,8806638028605,8806638028612,8806942042700,8806942042717', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M098431]다엽가루|[M100027]오르소시폰가루', '함량_원료성분원문': '총량 : 1캡슐(499.0mg) 중|성분명 : 다엽가루|분량 : 250.0|단위 : 밀리그램|규격 : 생규|성분정보 : 카페인으로서 5.0mg;총량 : 1캡슐(499.0mg) 중|성분명 : 오르소시폰가루|분량 : 150.0|단위 : 밀리그램|규격 : 생규|성분정보 : 메톡시플라본으로서 0.24mg', '함량_총량기준': '1캡슐(499.0mg) 중', '수집URL': 'https://drug.hospitalk.net/item/200001205', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200001205', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200701274', 'ITEM_NAME': '그린솔트에프액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염 액;알란토인;디펜히드라민염산염;디부카인염산염;나파졸린염산염', 'ENTP_NAME': '(주)그린제약', 'CHART': '무색의 투명한 액제', 'CHANGE_DATE': '2026-09-09', 'BAR_CODE': '8806483000801,8806483000818', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223220]클로르헥시딘글루콘산염 액|[M051015]알란토인|[M222973]디펜히드라민염산염|[M222965]디부카인염산염|[M222937]나파졸린염산염', '함량_원료성분원문': '총량 : 이 약 1mL 중|성분명 : 나파졸린염산염|분량 : 1.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1mL 중|성분명 : 디부카인염산염|분량 : 1.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1mL 중|성분명 : 디펜히드라민염산염|분량 : 3.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 1mL 중|성분명 : 알란토인|분량 : 2.0|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 이 약 1mL 중|성분명 : 클로르헥시딘글루콘산염 액|분량 : 0.01|단위 : 밀리리터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염으로서 2mg', '함량_총량기준': '이 약 1mL 중', '수집URL': 'https://drug.hospitalk.net/item/200701274', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200701274', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202107279', 'ITEM_NAME': '그린알로정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '노회건조엑스;우르소데옥시콜산;수산화마그네슘', 'ENTP_NAME': '(주)시어스제약', 'CHART': '분홍색의 장방형 필름코팅정제', 'CHANGE_DATE': '2026-07-30', 'BAR_CODE': '8806890019007,8806890019014', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M103222]노회건조엑스|[M223167]우르소데옥시콜산|[M040306]수산화마그네슘', '함량_원료성분원문': '총량 : 1정675밀리그램|성분명 : 수산화마그네슘|분량 : 500|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정675밀리그램|성분명 : 우르소데옥시콜산|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정675밀리그램|성분명 : 노회건조엑스|분량 : 100|단위 : 밀리그램|규격 : EP|성분정보 : 히드록시안트라센유도체(바바로인)(으)로서 20 밀리그램', '함량_총량기준': '1675', '수집URL': 'https://drug.hospitalk.net/item/202107279', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202107279', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200606531', 'ITEM_NAME': '그린엠캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '오르소시폰가루;다엽가루', 'ENTP_NAME': '(주)휴온스메디텍', 'CHART': '녹색의 분말이 충진된 상부 암녹색, 하부 미황색의 경질캡슐', 'CHANGE_DATE': '2023-06-26', 'BAR_CODE': '8806437025003,8806437025010,8806437025027,8806704006704,8806704006711', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M100027]오르소시폰가루|[M098431]다엽가루', '함량_원료성분원문': '총량 : 1 캡슐(507 mg) 중|성분명 : 다엽가루|분량 : 250|단위 : 밀리그램|규격 : 생규|성분정보 : 카페인으로서 5mg;총량 : 1 캡슐(507 mg) 중|성분명 : 오르소시폰가루|분량 : 150|단위 : 밀리그램|규격 : 생규|성분정보 : 시네세틴으로서 0.0675mg', '함량_총량기준': '1 캡슐(507 mg) 중', '수집URL': 'https://drug.hospitalk.net/item/200606531', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200606531', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199503356', 'ITEM_NAME': '그린와이나액2%(글루타랄콘센트레이트)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '글루타랄콘센트레이트', 'ENTP_NAME': '(주)그린제약', 'CHART': '특이한 냄새가 있는 투명한 액체이다', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806483001402,8806483001419', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081708]글루타랄콘센트레이트', '함량_원료성분원문': '총량 : 100 밀리리터중|성분명 : 글루타랄콘센트레이트|분량 : 4|단위 : 그램|규격 : USP|성분정보 : 글루타알데히드로서 2g', '함량_총량기준': '100 밀리리터중', '수집URL': 'https://drug.hospitalk.net/item/199503356', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199503356', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202301987', 'ITEM_NAME': '그린와이나플러스액(글루타랄콘센트레이트)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '글루타랄콘센트레이트', 'ENTP_NAME': '(주)그린제약', 'CHART': '약간의 특이한 냄새가 있는 무색의 투명한 액제이다.', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806483013504,8806483013511', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081708]글루타랄콘센트레이트', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 글루타랄콘센트레이트|분량 : 4.2|단위 : 그램|규격 : USP|성분정보 : 글루타랄알데히드로서 2.1 그램', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/202301987', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202301987', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201901010', 'ITEM_NAME': '그린코플시럽(딸기향, 바나나향)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '덱스트로메토르판브롬화수소산염수화물;슈도에페드린염산염;구아이페네신', 'ENTP_NAME': '(주)녹십자', 'CHART': '딸기향: 딸기향이 나는 무색 또는 미황색의 투명한 시럽제 바나나향: 바나나향이 나는 무색 또는 미황색의 투명한 시럽제', 'CHANGE_DATE': '2025-07-30', 'BAR_CODE': '8806436056107,8806436056114,8806436056121', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M222957]덱스트로메토르판브롬화수소산염수화물|[M203364]슈도에페드린염산염|[M050058]구아이페네신|[M222957]덱스트로메토르판브롬화수소산염수화물|[M203364]슈도에페드린염산염|[M050058]구아이페네신', '함량_원료성분원문': '총량 : 이 약 100mL 중 |성분명 : 구아이페네신|분량 : 1000|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 이 약 100mL 중 |성분명 : 슈도에페드린염산염|분량 : 300|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 100mL 중 |성분명 : 덱스트로메토르판브롬화수소산염수화물|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 100mL 중|성분명 : 구아이페네신|분량 : 1000|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 이 약 100mL 중|성분명 : 슈도에페드린염산염|분량 : 300|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 이 약 100mL 중|성분명 : 덱스트로메토르판브롬화수소산염수화물|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 100mL 중 -딸기향/이 약 100mL 중-바나나향', '수집URL': 'https://drug.hospitalk.net/item/201901010', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201901010', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200502775', 'ITEM_NAME': '그린콜샷에스시럽', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르페니라민말레산염;아세트아미노펜;dl-메틸에페드린염산염;덱스트로메토르판브롬화수소산염수화물', 'ENTP_NAME': '(주)녹십자', 'CHART': '갈색유리병에 든 딸기향이 있는 무색의 시럽제', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806436001800,8806436001817,8806436001824,8806436001831', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223211]클로르페니라민말레산염|[M040353]아세트아미노펜|[M204422]dl-메틸에페드린염산염|[M222957]덱스트로메토르판브롬화수소산염수화물', '함량_원료성분원문': '총량 : 100 밀리리터 중|성분명 : 클로르페니라민말레산염|분량 : 12.5|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 100 밀리리터 중|성분명 : 아세트아미노펜|분량 : 1,000|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100 밀리리터 중|성분명 : dl-메틸에페드린염산염|분량 : 125|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100 밀리리터 중|성분명 : 덱스트로메토르판브롬화수소산염수화물|분량 : 75|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '100 밀리리터 중', '수집URL': 'https://drug.hospitalk.net/item/200502775', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200502775', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200608329', 'ITEM_NAME': '그린콜연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아세트아미노펜;클로르페니라민말레산염;슈도에페드린염산염', 'ENTP_NAME': '(주)알피바이오', 'CHART': '무색 내지 미황색(연노랑)의 투명한 내용물을 함유한 투명한 장방형 연질캡슐', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806616000203,8806616000210', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040353]아세트아미노펜|[M223211]클로르페니라민말레산염|[M203364]슈도에페드린염산염', '함량_원료성분원문': '총량 : 1캡슐1,650밀리그램|성분명 : 아세트아미노펜|분량 : 325.00|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1캡슐1,650밀리그램|성분명 : 클로르페니라민말레산염|분량 : 2.50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐1,650밀리그램|성분명 : 슈도에페드린염산염|분량 : 30.00|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '11,650', '수집URL': 'https://drug.hospitalk.net/item/200608329', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200608329', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201802109', 'ITEM_NAME': '그린쿨인후스프레이액(포비돈요오드)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '포비돈요오드', 'ENTP_NAME': '(주)그린제약', 'CHART': '약간의 점성이 있는 옅은 갈색의 액제', 'CHANGE_DATE': '2024-08-22', 'BAR_CODE': '8806483011302,8806483011319', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M244694]포비돈요오드', '함량_원료성분원문': '총량 : 이 약 100mL 중|성분명 : 포비돈요오드|분량 : 0.45|단위 : 그램|규격 : KP|성분정보 : 유효요오드로서0.045그램', '함량_총량기준': '이 약 100mL 중', '수집URL': 'https://drug.hospitalk.net/item/201802109', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201802109', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200000129', 'ITEM_NAME': '그린쿨환(안중조기환)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '천궁;백두구;목향;백출;지실;신곡;복신;당귀;향부자;감초;황련;반하;내복자;자소자;작약;진피', 'ENTP_NAME': '(주)한풍제약', 'CHART': '갈색의 소형환제이다.', 'CHANGE_DATE': '2025-06-16', 'BAR_CODE': '8806581002509,8806581002516,8806581002523,8806581002530,8806581002547,8806581002554', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040550]천궁|[M050540]백두구|[M040187]목향|[M040214]백출|[M040536]지실|[M050891]신곡|[M081401]복신|[M040070]당귀|[M040228]향부자|[M040006]감초|[M040792]황련|[M040202]반하|[M210181]내복자|[M099441]자소자|[M040523]작약|[M040538]진피', '함량_원료성분원문': '총량 : 1환120밀리그램|성분명 : 감초|분량 : 1.87|단위 : 밀리그램|규격 : KP|성분정보 : 글리시리진산으로서 0.05mg;총량 : 1환120밀리그램|성분명 : 황련|분량 : 6.16|단위 : 밀리그램|규격 : KP|성분정보 : 베르베린(베르베린염화물)으로서 0.26mg;총량 : 1환120밀리그램|성분명 : 반하|분량 : 6.16|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환120밀리그램|성분명 : 내복자|분량 : 3.63|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환120밀리그램|성분명 : 자소자|분량 : 3.63|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환120밀리그램|성분명 : 작약|분량 : 4.95|단위 : 밀리그램|규격 : KP|성분정보 : 패오니플로린으로서 0.10mg;총량 : 1환120밀리그램|성분명 : 진피|분량 : 12.21|단위 : 밀리그램|규격 : KP|성분정보 : 헤스피리딘으로서 0.49mg;총량 : 1환120밀리그램|성분명 : 향부자|분량 : 18.37|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환120밀리그램|성분명 : 당귀|분량 : 2.97|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환120밀리그램|성분명 : 천궁|분량 : 2.97|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환120밀리그램|성분명 : 백두구|분량 : 2.97|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환120밀리그램|성분명 : 목향|분량 : 0.66|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환120밀리그램|성분명 : 백출|분량 : 18.37|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환120밀리그램|성분명 : 지실|분량 : 6.16|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1환120밀리그램|성분명 : 신곡|분량 : 6.16|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1환120밀리그램|성분명 : 복신|분량 : 6.16|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1120', '수집URL': 'https://drug.hospitalk.net/item/200000129', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200000129', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199600830', 'ITEM_NAME': '그린큐액(돔페리돈)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '돔페리돈', 'ENTP_NAME': '동성제약(주)', 'CHART': '연한 갈색의 액제', 'CHANGE_DATE': '2020-03-02', 'BAR_CODE': '8806432000203,8806432000210', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081091]돔페리돈', '함량_원료성분원문': '총량 : 1병75밀리리터|성분명 : 돔페리돈|분량 : 10.0|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '175', '수집URL': 'https://drug.hospitalk.net/item/199600830', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199600830', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200004840', 'ITEM_NAME': '그린클로르헥시딘크림(클로르헥시딘글루콘산염액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염 액', 'ENTP_NAME': '(주)그린제약', 'CHART': '무색의 크림제', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806483001501,8806483001518', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223220]클로르헥시딘글루콘산염 액', '함량_원료성분원문': '총량 : 이 약 1g 중|성분명 : 클로르헥시딘글루콘산염 액|분량 : 0.05|단위 : 밀리미터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염으로서 10mg', '함량_총량기준': '이 약 1g 중', '수집URL': 'https://drug.hospitalk.net/item/200004840', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200004840', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200004835', 'ITEM_NAME': '그린태고액1%(알킬디아미노에틸글리신염산염액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '알킬디아미노에틸글리신염산염액40%', 'ENTP_NAME': '(주)그린제약', 'CHART': '기포성이 있는 미황색의 투명액체.', 'CHANGE_DATE': '2015-06-12', 'BAR_CODE': '8806483001600,8806483001617,8806483001624,8806483001631,8806483001648', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M257839]알킬디아미노에틸글리신염산염액40%', '함량_원료성분원문': '총량 : 이 약 100mL 중|성분명 : 알킬디아미노에틸글리신염산염액40%|분량 : 2.5|단위 : 밀리리터|규격 : 별규|성분정보 : 알킬디아미노에틸글리신염산염으로서 1g', '함량_총량기준': '이 약 100mL 중', '수집URL': 'https://drug.hospitalk.net/item/200004835', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200004835', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200302512', 'ITEM_NAME': '그린티눈액(수출명 : 1. Green Tinun Solution, 2. Collopaint Wart Solution)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '살리실산;락트산', 'ENTP_NAME': '(주)그린제약', 'CHART': '점조성이 있는 무색투명한 액', 'CHANGE_DATE': '2025-08-29', 'BAR_CODE': '8806483002003,8806483002010,8806483002027', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040264]살리실산|[M223371]락트산', '함량_원료성분원문': '총량 : 100 ml 중|성분명 : 살리실산|분량 : 10|단위 : 그램|규격 : KP|성분정보 : ;총량 : 100 ml 중|성분명 : 락트산|분량 : 10|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '100 ml 중', '수집URL': 'https://drug.hospitalk.net/item/200302512', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200302512', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201801264', 'ITEM_NAME': '그린포비돈브러쉬액(포비돈요오드)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '포비돈요오드', 'ENTP_NAME': '(주)그린제약', 'CHART': '황갈색의 액체가 흡착된 플라스틱솔 스폰지', 'CHANGE_DATE': '2025-09-08', 'BAR_CODE': '8806483011500,8806483011517', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M244694]포비돈요오드', '함량_원료성분원문': '총량 : 플라스틱솔스폰지 1개 (플라스틱솔스폰지 14g + 약액 30mL 흡착) 약액 30mL 중|성분명 : 포비돈요오드|분량 : 2.25|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '플라스틱솔스폰지 1개 (플라스틱솔스폰지 14g + 약액 30mL 흡착) 약액 30mL 중', '수집URL': 'https://drug.hospitalk.net/item/201801264', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201801264', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199904088', 'ITEM_NAME': '그린포비돈세정액(포비돈요오드)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '포비돈 요오드', 'ENTP_NAME': '(주)그린제약', 'CHART': '황갈색의 액제', 'CHANGE_DATE': '1999-10-27', 'BAR_CODE': '8806483002102,8806483002119,8806483002126', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M215884]포비돈 요오드', '함량_원료성분원문': '총량 : 이 약 100밀리리터중|성분명 : 포비돈 요오드|분량 : 7.5|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 100밀리리터중', '수집URL': 'https://drug.hospitalk.net/item/199904088', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199904088', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200611367', 'ITEM_NAME': '그린포비돈스틱스왑(포비돈요오드)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '포비돈 요오드', 'ENTP_NAME': '(주)그린제약', 'CHART': '어두운 적갈색의 액이 흡착된 탈지면봉', 'CHANGE_DATE': '2014-10-23', 'BAR_CODE': '8806483002201,8806483002218,8806483002225,8806483002232,8806483002249,8806483002256,8806483002263,8806483002270,8806483002287', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M215884]포비돈 요오드', '함량_원료성분원문': '총량 : 1탈지면봉(총 2.4g 중 탈지면봉 0.83g, 약액 1.5ml흡착) 중|성분명 : 포비돈 요오드|분량 : 0.15|단위 : 그램|규격 : KP|성분정보 : 요오드로서 15mg', '함량_총량기준': '1탈지면봉(총 2.4g 중 탈지면봉 0.83g, 약액 1.5ml흡착) 중', '수집URL': 'https://drug.hospitalk.net/item/200611367', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200611367', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202200222', 'ITEM_NAME': '그린포비돈요오드가글액7.5%', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '포비돈요오드', 'ENTP_NAME': '(주)그린제약', 'CHART': '남적색의 액제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '미기재', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M244708]포비돈요오드', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 포비돈요오드|분량 : 7.5|단위 : 그램|규격 : KP|성분정보 : 유효요오드로서750mg', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/202200222', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202200222', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199503352', 'ITEM_NAME': '그린포비돈요오드액(수출명 : Green Povidone-Iodine Topical Solution)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '포비돈 요오드', 'ENTP_NAME': '(주)그린제약', 'CHART': '남적색 액체', 'CHANGE_DATE': '2019-01-25', 'BAR_CODE': '8806483002300,8806483002317,8806483002324,8806483002331,8806483002348,8806483002355', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M215884]포비돈 요오드', '함량_원료성분원문': '총량 : 이 약 100 밀리리터 중|성분명 : 포비돈 요오드|분량 : 10|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 100 밀리리터 중', '수집URL': 'https://drug.hospitalk.net/item/199503352', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199503352', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199900936', 'ITEM_NAME': '그린폰캡슐(수출명:레디캡슐)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '오르소시폰가루;다엽가루', 'ENTP_NAME': '(주)에이프로젠바이오로직스', 'CHART': '녹색의 분말이 충전된 상하 초록색의 캡슐제', 'CHANGE_DATE': '2021-01-05', 'BAR_CODE': '8806452043105,8806452043112,8806452043129,8806518000509,8806518000516,8806518000523,8806518000530', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M100027]오르소시폰가루|[M098431]다엽가루', '함량_원료성분원문': '총량 : 1캡슐(505.0mg) 중|성분명 : 다엽가루|분량 : 250.0|단위 : 밀리그램|규격 : 생규|성분정보 : 카페인으로서 5.0mg;총량 : 1캡슐(505.0mg) 중|성분명 : 오르소시폰가루|분량 : 150.0|단위 : 밀리그램|규격 : 생규|성분정보 : 메톡시플라본으로서 0.24mg', '함량_총량기준': '1캡슐(505.0mg) 중', '수집URL': 'https://drug.hospitalk.net/item/199900936', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199900936', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200901086', 'ITEM_NAME': '그린헥시디놀액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염 액;에탄올(95)', 'ENTP_NAME': '(주)그린제약', 'CHART': '라벤다 향기와 알코올 냄새가 나는 분홍색의 액', 'CHANGE_DATE': '2025-10-17', 'BAR_CODE': '8806483009507,8806483009514', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223220]클로르헥시딘글루콘산염 액|[M284425]에탄올(95)', '함량_원료성분원문': '총량 : 100 밀리리터 중|성분명 : 클로르헥시딘글루콘산염 액|분량 : 2.5|단위 : 밀리리터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염으로 0.5w/v%;총량 : 100 밀리리터 중|성분명 : 에탄올(95)|분량 : 75|단위 : 밀리리터|규격 : KP|성분정보 : 에탄올로서 72v/v%', '함량_총량기준': '100 밀리리터 중', '수집URL': 'https://drug.hospitalk.net/item/200901086', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200901086', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201505097', 'ITEM_NAME': '그린헥시디놀액2%', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염 액;에탄올(95)', 'ENTP_NAME': '(주)그린제약', 'CHART': '1. 플라스틱 용기에 든 엷은 청색의 알코올 냄새가 나는 맑은 액 2. 플라스틱 용기에 든 무색의 알코올 냄새가 나는 맑은 액 3. 스폰지가 달린 플라스틱 어플리케이터에 연결된 플라스틱 용기에 들어있는 엷은 청색의 알콜냄새가 나는 투명한 액체', 'CHANGE_DATE': '2026-06-12', 'BAR_CODE': '8806483011104,8806483011111,8806483011128,8806483013702,8806483013719,8806483013726,8806483013733', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223220]클로르헥시딘글루콘산염 액|[M284425]에탄올(95)|[M223220]클로르헥시딘글루콘산염 액|[M284425]에탄올(95)|[M223220]클로르헥시딘글루콘산염 액|[M284425]에탄올(95)', '함량_원료성분원문': '총량 : 이 약 100mL 중|성분명 : 클로르헥시딘글루콘산염 액|분량 : 10|단위 : 밀리리터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염으로서 2.0g;총량 : 이 약 100mL 중|성분명 : 에탄올(95)|분량 : 75|단위 : 밀리리터|규격 : KP|성분정보 : 에탄올로서 72mL;총량 : 이 약 100mL 중|성분명 : 클로르헥시딘글루콘산염 액|분량 : 10|단위 : 밀리리터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염으로서 2.0g;총량 : 이 약 100mL 중|성분명 : 에탄올(95)|분량 : 75|단위 : 밀리리터|규격 : KP|성분정보 : 에탄올로서 72mL;총량 : 이 약 100mL 중|성분명 : 클로르헥시딘글루콘산염 액|분량 : 10|단위 : 밀리리터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염으로서 2.0g;총량 : 이 약 100mL 중|성분명 : 에탄올(95)|분량 : 75|단위 : 밀리리터|규격 : KP|성분정보 : 에탄올로서 72mL', '함량_총량기준': '이 약 100mL 중-제1법/이 약 100mL 중-제2법/이 약 100mL 중-제3법', '수집URL': 'https://drug.hospitalk.net/item/201505097', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201505097', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201804672', 'ITEM_NAME': '그린헥시딘0.5%액(클로르헥시딘글루콘산염액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염 액', 'ENTP_NAME': '(주)그린제약', 'CHART': '무색 또는 미황색의 맑은 액', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806483012002,8806483012019,8806483012101,8806483012118,8806483012200,8806483012217', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223220]클로르헥시딘글루콘산염 액', '함량_원료성분원문': '총량 : 이 약 100mL 중|성분명 : 클로르헥시딘글루콘산염 액|분량 : 2.5|단위 : 밀리리터|규격 : KP|성분정보 :', '함량_총량기준': '이 약 100mL 중', '수집URL': 'https://drug.hospitalk.net/item/201804672', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201804672', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201901012', 'ITEM_NAME': '그린헥시딘가글액(클로르헥시딘글루콘산염액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염액', 'ENTP_NAME': '(주)그린제약', 'CHART': '스피아민트향이 나는 투명한 액제', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806483012309,8806483012316', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M244239]클로르헥시딘글루콘산염액', '함량_원료성분원문': '총량 : 이 약 100mL 중|성분명 : 클로르헥시딘글루콘산염액|분량 : 0.5|단위 : 밀리리터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염으로서 0.1그램', '함량_총량기준': '이 약 100mL 중', '수집URL': 'https://drug.hospitalk.net/item/201901012', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201901012', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202005237', 'ITEM_NAME': '그린헥시딘가글액0.12%(클로르헥시딘글루콘산염액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염 액', 'ENTP_NAME': '(주)그린제약', 'CHART': '스피아민트향이 나는 투명한 액제', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806483013108,8806483013115,8806483013122,8806483013139', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223220]클로르헥시딘글루콘산염 액', '함량_원료성분원문': '총량 : 이 약 100mL 중|성분명 : 클로르헥시딘글루콘산염 액|분량 : 0.6|단위 : 밀리리터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염(으)로서 0.12 그램', '함량_총량기준': '이 약 100mL 중', '수집URL': 'https://drug.hospitalk.net/item/202005237', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202005237', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201801263', 'ITEM_NAME': '그린헥시딘브러쉬액(클로르헥시딘글루콘산염액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염액', 'ENTP_NAME': '(주)그린제약', 'CHART': '분홍색의 액체가 흡착된 플라스틱솔스폰지', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806483011609,8806483011616', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M244239]클로르헥시딘글루콘산염액', '함량_원료성분원문': '총량 : 플라스틱솔스폰지1개 중(플라스틱솔스폰지 14g + 약액 25mL) 약액 25mL 중|성분명 : 클로르헥시딘글루콘산염액|분량 : 5|단위 : 밀리리터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염으로서 4(w/v%)', '함량_총량기준': '플라스틱솔스폰지1개 중(플라스틱솔스폰지 14g + 약액 25mL) 약액 25mL 중', '수집URL': 'https://drug.hospitalk.net/item/201801263', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201801263', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201803651', 'ITEM_NAME': '그린헥시딘세정액4%(클로르헥시딘글루콘산염액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염액', 'ENTP_NAME': '(주)그린제약', 'CHART': '핑크색의 맑은 반 점도성 용액', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806483011807,8806483011814,8806483011821', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M244239]클로르헥시딘글루콘산염액', '함량_원료성분원문': '총량 : 100mL중|성분명 : 클로르헥시딘글루콘산염액|분량 : 20.0|단위 : 밀리리터|규격 : KP|성분정보 :  클로르헥시딘글루콘산염으로서 4g', '함량_총량기준': '100mL중', '수집URL': 'https://drug.hospitalk.net/item/201803651', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201803651', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201506622', 'ITEM_NAME': '그린헥시딘스틱스왑액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염 액;에탄올(95)', 'ENTP_NAME': '(주)그린제약', 'CHART': '특이한 향 및 알콜냄새가 나는 무색의 투명한 액체가 흡착된 흰색의 탈지면봉', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806483011203,8806483011210,8806483011227,8806483011234', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223220]클로르헥시딘글루콘산염 액|[M284425]에탄올(95)', '함량_원료성분원문': '총량 : 탈지면봉 1개 중(탈지면 0.2g + 약액 1.75mL 흡착), 약액 1.75mL 중|성분명 : 클로르헥시딘글루콘산염 액|분량 : 0.175|단위 : 밀리리터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염으로 2w/v%;총량 : 탈지면봉 1개 중(탈지면 0.2g + 약액 1.75mL 흡착), 약액 1.75mL 중|성분명 : 에탄올(95)|분량 : 1.312|단위 : 밀리리터|규격 : KP|성분정보 : 에탄올로서 72v/v%', '함량_총량기준': '탈지면봉 1개 중(탈지면 0.2g + 약액 1.75mL 흡착), 약액 1.75mL 중', '수집URL': 'https://drug.hospitalk.net/item/201506622', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201506622', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200302514', 'ITEM_NAME': '그린헥시딘액5%(클로르헥시딘글루콘산염액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로르헥시딘글루콘산염 액', 'ENTP_NAME': '(주)그린제약', 'CHART': '라벤다 향기가 나는 적색의 투명한 액이다.', 'CHANGE_DATE': '2026-02-13', 'BAR_CODE': '8806483002508,8806483002515,8806483002522', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223220]클로르헥시딘글루콘산염 액', '함량_원료성분원문': '총량 : 이 약 100mL 중|성분명 : 클로르헥시딘글루콘산염 액|분량 : 25|단위 : 밀리리터|규격 : KP|성분정보 : 클로르헥시딘글루콘산염으로서 5.0그램', '함량_총량기준': '이 약 100mL 중', '수집URL': 'https://drug.hospitalk.net/item/200302514', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200302514', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202502075', 'ITEM_NAME': '그밤엔연질캡슐(디펜히드라민염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '디펜히드라민염산염', 'ENTP_NAME': '경동제약(주)', 'CHART': '무색 내지 연한 청록색의 투명한 액상의 내용물을 함유한 연청록색의 볼록한 타원형 연질캡슐', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806481052604,8806481052611', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M222973]디펜히드라민염산염', '함량_원료성분원문': '총량 : 1캡슐560밀리그램|성분명 : 디펜히드라민염산염|분량 : 50.00|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1560', '수집URL': 'https://drug.hospitalk.net/item/202502075', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202502075', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200712467', 'ITEM_NAME': '근골환(양혈장근건보환)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '구기자;우슬;강활;창출;황기;오미자;인삼;백출;산약;방풍;방기;숙지황;당귀;작약;황백;두충;보골지;토사자;골쇄보;귀판', 'ENTP_NAME': '한솔신약(주)', 'CHART': '갈색의 환제', 'CHANGE_DATE': '2010-06-20', 'BAR_CODE': '8806458014406,8806458014413,8806458014420,8806458014437,8806458014444,8806458014451', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040030]구기자|[M040476]우슬|[M050022]강활|[M040548]창출|[M040790]황기|[M040445]오미자|[M040213]인삼|[M040214]백출|[M040258]산약|[M040205]방풍|[M050533]방기|[M051364]숙지황|[M040070]당귀|[M040523]작약|[M040793]황백|[M040089]두충|[M050609]보골지|[M050719]토사자|[M086023]골쇄보|[M083081]귀판', '함량_원료성분원문': '총량 : 1포(3.0g) 중|성분명 : 숙지황|분량 : 150|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 당귀|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 작약|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 황백|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 두충|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 보골지|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 토사자|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 골쇄보|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 귀판|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 방기|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 방풍|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 우슬|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 강활|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 창출|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 황기|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 오미자|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 인삼|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 백출|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 산약|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 구기자|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1포(3.0g) 중', '수집URL': 'https://drug.hospitalk.net/item/200712467', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200712467', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201307834', 'ITEM_NAME': '글로게이트정(알마게이트)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '알마게이트', 'ENTP_NAME': '(주)킵스바이오파마', 'CHART': '흰색의 원형 정제', 'CHANGE_DATE': '2015-12-17', 'BAR_CODE': '8806932009102,8806932009119,8806932009126,8806932009133', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081294]알마게이트', '함량_원료성분원문': '총량 : 1정 (550밀리그램) 중|성분명 : 알마게이트|분량 : 500.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정 (550밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201307834', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201307834', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201207377', 'ITEM_NAME': '글로덱시정300mg(덱시부프로펜)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '덱시부프로펜', 'ENTP_NAME': '(주)킵스바이오파마', 'CHART': '분홍색의 장방형 필름코팅정', 'CHANGE_DATE': '2026-01-02', 'BAR_CODE': '8806932006309,8806932006316,8806932006323,8806932006330', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M254719]덱시부프로펜', '함량_원료성분원문': '총량 : 1정465밀리그램|성분명 : 덱시부프로펜|분량 : 300|단위 : 밀리그램|규격 : KP|성분정보 : 덱시부프로펜으로서300mg', '함량_총량기준': '1465', '수집URL': 'https://drug.hospitalk.net/item/201207377', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201207377', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201402959', 'ITEM_NAME': '글로아스피린장용정100mg(아스피린)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아스피린', 'ENTP_NAME': '(주)킵스바이오파마', 'CHART': '흰색의 원형 장용성 필름코팅정', 'CHANGE_DATE': '2026-01-08', 'BAR_CODE': '8806932009607,8806932009614,8806932009621', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040355]아스피린', '함량_원료성분원문': '총량 : 1정 (169밀리그램) 중|성분명 : 아스피린|분량 : 100.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정 (169밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201402959', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201402959', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202402424', 'ITEM_NAME': '글로징코정240밀리그램(은행엽건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은행엽 건조엑스', 'ENTP_NAME': '(주)킵스바이오파마', 'CHART': '녹색의 장방형 필름코팅정제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806932026109', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M273892]은행엽 건조엑스', '함량_원료성분원문': '총량 : 1정730.0밀리그램|성분명 : 은행엽 건조엑스|분량 : 240|단위 : 밀리그램|규격 : EP|성분정보 :', '함량_총량기준': '1730.0', '수집URL': 'https://drug.hospitalk.net/item/202402424', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202402424', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202401821', 'ITEM_NAME': '글로칼디정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '탄산칼슘 과립95%;콜레칼시페롤농축분말', 'ENTP_NAME': '(주)킵스바이오파마', 'CHART': '녹색의 장방형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806932026000,8806932026017,8806932026024', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M115129]탄산칼슘 과립95%|[M102050]콜레칼시페롤농축분말', '함량_원료성분원문': '총량 : 1정453.03밀리그램|성분명 : 탄산칼슘 과립95%|분량 : 263.15|단위 : 밀리그램|규격 : 별규|성분정보 : 칼슘(으)로서 100 밀리그램;총량 : 1정453.03밀리그램|성분명 : 콜레칼시페롤농축분말|분량 : 10|단위 : 밀리그램|규격 : EP|성분정보 : 비타민D(으)로서 1,000 아이.유', '함량_총량기준': '1453.03', '수집URL': 'https://drug.hospitalk.net/item/202401821', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202401821', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201305220', 'ITEM_NAME': '글루100정(글루타티온(환원형))', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '글루타티온(환원형)', 'ENTP_NAME': '(주)동구바이오제약', 'CHART': '흰색의 원형 필름코팅정', 'CHANGE_DATE': '2017-11-29', 'BAR_CODE': '8806573060104,8806573060111,8806573060128,8806573060135,8806573060142', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256276]글루타티온(환원형)|[M256276]글루타티온(환원형)', '함량_원료성분원문': '총량 : [내수용] 1정(299.0mg) 중,   [수출용] 1정(588.06mg) 중|성분명 : 글루타티온(환원형)|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : [내수용] 1정(299.0mg) 중,   [수출용] 1정(588.06mg) 중|성분명 : 글루타티온(환원형)|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '[내수용] 1정(299.0mg) 중,   [수출용] 1정(588.06mg) 중-내수용/[내수용] 1정(299.0mg) 중,   [수출용] 1정(588.06mg) 중-수출용', '수집URL': 'https://drug.hospitalk.net/item/201305220', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201305220', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202302457', 'ITEM_NAME': '글루디톡정(글루타티온(환원형))', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '글루타티온(환원형)', 'ENTP_NAME': '태극제약(주)', 'CHART': '흰색의 원형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806448066903,8806448066910,8806448066927,8806448066934', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256276]글루타티온(환원형)', '함량_원료성분원문': '총량 : 1정256밀리그램|성분명 : 글루타티온(환원형)|분량 : 100.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1256', '수집URL': 'https://drug.hospitalk.net/item/202302457', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202302457', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202402630', 'ITEM_NAME': '글루라이트정(글루타티온(환원형))', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '글루타티온(환원형)', 'ENTP_NAME': '풍림무약(주)', 'CHART': '흰색의 원형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806490025200,8806490025217', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256276]글루타티온(환원형)', '함량_원료성분원문': '총량 : 1정301밀리그램|성분명 : 글루타티온(환원형)|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1301', '수집URL': 'https://drug.hospitalk.net/item/202402630', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202402630', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200607010', 'ITEM_NAME': '글루민캡슐(결정황산글루코사민)(수출용)(수출명:민코스캡슐)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '결정황산글루코사민', 'ENTP_NAME': '(주)씨엠지제약', 'CHART': '백색내지 담황색의 가루 혹은 과립상이 든 상·하부 갈색의 경질캡슐', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806486000204', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050075]결정황산글루코사민', '함량_원료성분원문': '총량 : 1캡슐 중 내용물로서438밀리그램|성분명 : 결정황산글루코사민|분량 : 312.5|단위 : 밀리그램|규격 : KP|성분정보 : 황산글루코사민으로서 250밀리그램', '함량_총량기준': '1캡슐 중 내용물로서438밀리그램', '수집URL': 'https://drug.hospitalk.net/item/200607010', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200607010', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202101356', 'ITEM_NAME': '글루비타정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '폴산;시아노코발라민 100배산;피리독신염산염;푸르설티아민', 'ENTP_NAME': '(주)다림바이오텍', 'CHART': '노란색의 원형 필름코팅정제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806646026600,8806646026617', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223289]폴산|[M115473]시아노코발라민 100배산|[M204304]피리독신염산염|[M051415]푸르설티아민', '함량_원료성분원문': '총량 : 1정291.2밀리그램|성분명 : 푸르설티아민|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정291.2밀리그램|성분명 : 피리독신염산염|분량 : 33.33|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정291.2밀리그램|성분명 : 시아노코발라민 100배산|분량 : 100|단위 : 밀리그램|규격 : USP|성분정보 : 시아노코발라민(으)로서 1000 마이크로그램;총량 : 1정291.2밀리그램|성분명 : 폴산|분량 : 0.33|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1291.2', '수집URL': 'https://drug.hospitalk.net/item/202101356', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202101356', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201603261', 'ITEM_NAME': '글루산캡슐(결정황산글루코사민)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '결정황산글루코사민', 'ENTP_NAME': '(주)넥스팜코리아', 'CHART': '백색 내지 담갈색의 분말이 든 상부적색, 하부 미황색의 경질캡슐제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806625035104,8806625035111', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050075]결정황산글루코사민', '함량_원료성분원문': '총량 : 1캡슐(758mg) 중|성분명 : 결정황산글루코사민|분량 : 625.0|단위 : 밀리그램|규격 : KP|성분정보 : 황산글루코사민으로서 500mg', '함량_총량기준': '1캡슐(758mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201603261', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201603261', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202400046', 'ITEM_NAME': '글루온정(글루타티온(환원형))', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '글루타티온(환원형)', 'ENTP_NAME': '미래바이오제약(주)', 'CHART': '흰색의 원형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '미기재', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256276]글루타티온(환원형)', '함량_원료성분원문': '총량 : 1정301밀리그램|성분명 : 글루타티온(환원형)|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1301', '수집URL': 'https://drug.hospitalk.net/item/202400046', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202400046', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199701904', 'ITEM_NAME': '글루콤액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': 'L-리신염산염;L-이소류신;L-류신;L-메티오닌;L-발린;L-트레오닌;L-페닐알라닌;L-글루타민;코바마미드', 'ENTP_NAME': '고려제약(주)', 'CHART': '상부용기내의 엷은  분홍색의 과립상 분말과 바이알 내의 과일향이 있는 무색 내지 미황색의 투 명한 액이 든 복합제이다.', 'CHANGE_DATE': '2025-10-27', 'BAR_CODE': '8806428001405,8806428001412,8806428001429,8806428001436,8806428001443', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M222998]L-리신염산염|[M222530]L-이소류신|[M222531]L-류신|[M218567]L-메티오닌|[M209360]L-발린|[M103060]L-트레오닌|[M204442]L-페닐알라닌|[M202240]L-글루타민|[M100992]코바마미드', '함량_원료성분원문': '총량 : [액제용 분말] 상부캡 158.5mg/[액제] 바이알(10mL) 중|성분명 : 코바마미드|분량 : 2.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : [액제용 분말] 상부캡 158.5mg/[액제] 바이알(10mL) 중|성분명 : L-글루타민|분량 : 20.0|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : [액제용 분말] 상부캡 158.5mg/[액제] 바이알(10mL) 중|성분명 : L-페닐알라닌|분량 : 22.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : [액제용 분말] 상부캡 158.5mg/[액제] 바이알(10mL) 중|성분명 : L-트레오닌|분량 : 10.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : [액제용 분말] 상부캡 158.5mg/[액제] 바이알(10mL) 중|성분명 : L-발린|분량 : 16.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : [액제용 분말] 상부캡 158.5mg/[액제] 바이알(10mL) 중|성분명 : L-메티오닌|분량 : 22.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : [액제용 분말] 상부캡 158.5mg/[액제] 바이알(10mL) 중|성분명 : L-류신|분량 : 22.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : [액제용 분말] 상부캡 158.5mg/[액제] 바이알(10mL) 중|성분명 : L-이소류신|분량 : 14.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : [액제용 분말] 상부캡 158.5mg/[액제] 바이알(10mL) 중|성분명 : L-리신염산염|분량 : 20.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '[액제용 분말] 상부캡 158.5mg/[액제] 바이알(10mL) 중-액제용 분말/[액제용 분말] 상부캡 158.5mg/[액제] 바이알(10mL) 중-액제', '수집URL': 'https://drug.hospitalk.net/item/199701904', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199701904', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201802943', 'ITEM_NAME': '글루타넥스정(글루타티온(환원형))(수출명:Glutanex Tab.)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '글루타티온(환원형)', 'ENTP_NAME': '정우신약(주)', 'CHART': '흰색의 원형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806942051306,8806942051320', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256276]글루타티온(환원형)', '함량_원료성분원문': '총량 : 1정(299.0mg) 중|성분명 : 글루타티온(환원형)|분량 : 100.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정(299.0mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201802943', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201802943', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201504328', 'ITEM_NAME': '글루타시드정(글루타티온(환원형))(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '글루타티온(환원형)', 'ENTP_NAME': '(주)테라젠이텍스', 'CHART': '흰색의 당의정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806985030603', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256276]글루타티온(환원형)', '함량_원료성분원문': '총량 : 1정(450mg) 중|성분명 : 글루타티온(환원형)|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정(450mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201504328', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201504328', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202401743', 'ITEM_NAME': '글루타에스정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시메티콘파우더;디아스타제·프로테아제100;산화마그네슘;비스무트차탄산염;L-글루타민', 'ENTP_NAME': '(주)대웅제약', 'CHART': '연두색의 장방형 필름코팅정제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806416081105,8806416081112,8806416081129', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M270842]시메티콘파우더|[M261920]디아스타제·프로테아제100|[M040262]산화마그네슘|[M284755]비스무트차탄산염|[M202240]L-글루타민', '함량_원료성분원문': '총량 : 1정810밀리그램|성분명 : L-글루타민|분량 : 250.00|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1정810밀리그램|성분명 : 비스무트차탄산염|분량 : 200.00|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1정810밀리그램|성분명 : 산화마그네슘|분량 : 30.00|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1정810밀리그램|성분명 : 디아스타제·프로테아제100|분량 : 20.00|단위 : 밀리그램|규격 : KP|성분정보 : 전분당화력 240단위 이상, 단백소화력 2000단위 이상;총량 : 1정810밀리그램|성분명 : 시메티콘파우더|분량 : 30.00|단위 : 밀리그램|규격 : 별규|성분정보 : 시메티콘(으)로서 19.6 밀리그램', '함량_총량기준': '1810', '수집URL': 'https://drug.hospitalk.net/item/202401743', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202401743', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201504984', 'ITEM_NAME': '글리돈정(작약감초탕)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '작약감초탕 건조엑스(3.4∼5.1→1)', 'ENTP_NAME': '(주)한풍제약', 'CHART': '갈색의 장방형 필름코팅정', 'CHANGE_DATE': '2016-06-01', 'BAR_CODE': '8806581058001,8806581058018', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M285492]작약감초탕 건조엑스(3.4∼5.1→1)', '함량_원료성분원문': '총량 : 1정744밀리그램|성분명 : 작약감초탕 건조엑스(3.4∼5.1→1)|분량 : 394|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1744', '수집URL': 'https://drug.hospitalk.net/item/201504984', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201504984', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200701224', 'ITEM_NAME': '금왕심단(천왕보심단)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '단삼;현삼;인삼;백자인;천문동;오미자;맥문동;생지황;당귀;산조인;복령;원지;길경;황련', 'ENTP_NAME': '한솔신약(주)', 'CHART': '흑갈색의 환제', 'CHANGE_DATE': '2019-10-15', 'BAR_CODE': '8806458000300,8806458000317,8806458000324,8806458000331,8806458000348,8806458000355', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050176]단삼|[M051932]현삼|[M040213]인삼|[M050550]백자인|[M051380]천문동|[M040445]오미자|[M040139]맥문동|[M051363]생지황|[M040070]당귀|[M040259]산조인|[M040225]복령|[M040482]원지|[M040048]길경|[M040792]황련', '함량_원료성분원문': '총량 : 1포(3.0g) 중|성분명 : 황련|분량 : 250|단위 : 밀리그램|규격 : KP|성분정보 : 베르베린(베르베린염화물)(으)로서 10.5 밀리그램;총량 : 1포(3.0g) 중|성분명 : 길경|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 원지|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 복령|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 산조인|분량 : 125|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 당귀|분량 : 125|단위 : 밀리그램|규격 : KP|성분정보 : 데쿠르신(으)로서 7.4 밀리그램;총량 : 1포(3.0g) 중|성분명 : 생지황|분량 : 500|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 맥문동|분량 : 125|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 오미자|분량 : 125|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 천문동|분량 : 125|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 백자인|분량 : 125|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 인삼|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 현삼|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(3.0g) 중|성분명 : 단삼|분량 : 62.5|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1포(3.0g) 중', '수집URL': 'https://drug.hospitalk.net/item/200701224', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200701224', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201202397', 'ITEM_NAME': '기가렉스연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '카르보시스테인;브롬헥신염산염', 'ENTP_NAME': '(주)알피바이오', 'CHART': '흰색 내지 연한 분홍색의 내용물을 함유한 적색 타원형 연질캡슐', 'CHANGE_DATE': '2025-12-30', 'BAR_CODE': '8806616037506,8806616037513', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268097]카르보시스테인|[M223062]브롬헥신염산염', '함량_원료성분원문': '총량 : 1캡슐(565mg) 중|성분명 : 카르보시스테인|분량 : 125.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(565mg) 중|성분명 : 브롬헥신염산염|분량 : 2.00|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '1캡슐(565mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201202397', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201202397', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200004264', 'ITEM_NAME': '기가에이연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': 'd-클로르페니라민말레산염;구아이페네신;트리메토퀴놀염산염수화물;노스카핀염산염수화물;덱스트로메토르판브롬화수소산염수화물', 'ENTP_NAME': '(주)알피바이오', 'CHART': '무색내지 주황색의 점조성액이 들어있는 주황색의 투명한 타원형 연질 캡슐제', 'CHANGE_DATE': '2024-06-05', 'BAR_CODE': '8806529000505,8806529000512,8806529000529,8806616028009,8806616028016', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223212]d-클로르페니라민말레산염|[M050058]구아이페네신|[M223249]트리메토퀴놀염산염수화물|[M223470]노스카핀염산염수화물|[M222957]덱스트로메토르판브롬화수소산염수화물', '함량_원료성분원문': '총량 : 1캡슐(710밀리그램) 중|성분명 : 덱스트로메토르판브롬화수소산염수화물|분량 : 15.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(710밀리그램) 중|성분명 : 노스카핀염산염수화물|분량 : 20.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(710밀리그램) 중|성분명 : 트리메토퀴놀염산염수화물|분량 : 2.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(710밀리그램) 중|성분명 : 구아이페네신|분량 : 75.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(710밀리그램) 중|성분명 : d-클로르페니라민말레산염|분량 : 2.00|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1캡슐(710밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200004264', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200004264', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201508445', 'ITEM_NAME': '기가엔드연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '카르보시스테인;브롬헥신염산염', 'ENTP_NAME': '동방에프티엘(주)', 'CHART': '흰색의 내용물을 함유한 적색의 타원형 연질캡슐', 'CHANGE_DATE': '2024-08-01', 'BAR_CODE': '8806805006405,8806805006412,8806805006429', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268097]카르보시스테인|[M223062]브롬헥신염산염', '함량_원료성분원문': '총량 : 1캡슐613밀리그램|성분명 : 카르보시스테인|분량 : 125|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐613밀리그램|성분명 : 브롬헥신염산염|분량 : 2|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '1613', '수집URL': 'https://drug.hospitalk.net/item/201508445', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201508445', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201605499', 'ITEM_NAME': '기가제로연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '카르보시스테인;브롬헥신염산염', 'ENTP_NAME': '코스맥스파마(주)', 'CHART': '흰색의 내용물을 함유한 주황색의 타원형 연질캡슐', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8800540000209,8800540000216,8800540000223,8800540000230,8800542000207,8800542000214,8800542000221,8800551021705,8800551021712,8800551021729,8800551021736,8806129001506,8806129001513', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268097]카르보시스테인|[M223062]브롬헥신염산염', '함량_원료성분원문': '총량 : 1캡슐(545mg) 중|성분명 : 카르보시스테인|분량 : 125.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(545mg) 중|성분명 : 브롬헥신염산염|분량 : 2.00|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '1캡슐(545mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201605499', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201605499', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200004525', 'ITEM_NAME': '기가천과립(소청룡탕)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '반하;오미자;세신;계지;감초;건강;작약;마황', 'ENTP_NAME': '한솔신약(주)', 'CHART': '갈색의 과립', 'CHANGE_DATE': '2019-04-18', 'BAR_CODE': '8806458000409,8806458000416,8806458000423,8806458000447,8806458000454', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040202]반하|[M040445]오미자|[M040293]세신|[M050037]계지|[M040006]감초|[M040007]건강|[M040523]작약|[M040135]마황', '함량_원료성분원문': '총량 : 1포(3.0그램) 중|성분명 : 마황|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그램) 중|성분명 : 작약|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그램) 중|성분명 : 건강|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그램) 중|성분명 : 감초|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그램) 중|성분명 : 계지|분량 : 1.00|단위 : 그램|규격 : 생규|성분정보 : ;총량 : 1포(3.0그램) 중|성분명 : 세신|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그램) 중|성분명 : 오미자|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1포(3.0그램) 중|성분명 : 반하|분량 : 2.00|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1포(3.0그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200004525', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200004525', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201603223', 'ITEM_NAME': '기가파워연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '브롬헥신염산염;카르보시스테인', 'ENTP_NAME': '한솔신약(주)', 'CHART': '흰색 내지 연한 분홍색의 내용물을 함유한 적색의 타원형 연질캡슐', 'CHANGE_DATE': '2026-02-12', 'BAR_CODE': '8806458041501,8806458041518', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223062]브롬헥신염산염|[M268097]카르보시스테인', '함량_원료성분원문': '총량 : 1캡슐(565 mg) 중|성분명 : 카르보시스테인|분량 : 125.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(565 mg) 중|성분명 : 브롬헥신염산염|분량 : 2.00|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '1캡슐(565 mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201603223', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201603223', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201606791', 'ITEM_NAME': '기가프신연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': 'L-카르보시스테인;브롬헥신염산염', 'ENTP_NAME': '(주)에이프로젠바이오로직스', 'CHART': '흰색의 내용물을 함유한 주황색의 타원형 연질캡슐', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806452093308,8806452093315', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M220819]L-카르보시스테인|[M223062]브롬헥신염산염', '함량_원료성분원문': '총량 : 1캡슐(545mg) 중|성분명 : L-카르보시스테인|분량 : 125.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(545mg) 중|성분명 : 브롬헥신염산염|분량 : 2.0|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '1캡슐(545mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201606791', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201606791', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201309432', 'ITEM_NAME': '기감탕노즈액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아세트아미노펜;작약;오미자;세신;반하;마황;육계;건강;클로르페니라민말레산염;감초', 'ENTP_NAME': '한국신텍스제약(주)', 'CHART': '진한 갈색의 액제가 든 파우치', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806230033205,8806230033212,8806230033229', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040353]아세트아미노펜|[M040523]작약|[M040445]오미자|[M040293]세신|[M040202]반하|[M040135]마황|[M050036]육계|[M040007]건강|[M223211]클로르페니라민말레산염|[M040006]감초', '함량_원료성분원문': '총량 : 1회 용량(100ml) 중|성분명 : 감초|분량 : 0.48|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(100ml) 중|성분명 : 클로르페니라민말레산염|분량 : 1.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회 용량(100ml) 중|성분명 : 건강|분량 : 0.16|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(100ml) 중|성분명 : 육계|분량 : 0.48|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(100ml) 중|성분명 : 마황|분량 : 0.8|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(100ml) 중|성분명 : 반하|분량 : 0.8|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(100ml) 중|성분명 : 세신|분량 : 0.48|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(100ml) 중|성분명 : 오미자|분량 : 0.8|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(100ml) 중|성분명 : 작약|분량 : 0.8|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(100ml) 중|성분명 : 아세트아미노펜|분량 : 200|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1회 용량(100ml) 중', '수집URL': 'https://drug.hospitalk.net/item/201309432', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201309432', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200109392', 'ITEM_NAME': '기공활혈고(수입명:CHIKUNGHUOSHIUEHKAO)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '살리실산메틸;산화아연;L-멘톨;유향;몰약;피마자;목별자;위령선', 'ENTP_NAME': '(주)오현파마코푸레이션', 'CHART': '녹색의 경고제', 'CHANGE_DATE': '2022-10-22', 'BAR_CODE': '8806606000107,8806606000114,8806606000121,8806606000138', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M203279]살리실산메틸|[M243785]산화아연|[M279284]L-멘톨|[M051238]유향|[M040188]몰약|[M088936]피마자|[M050499]목별자|[M083244]위령선', '함량_원료성분원문': '총량 : 1매 (부직포 및 플라스틱필름 포함 : 7g, 부직포 및 플라스틱필름 제외 : 5g, 10cm x 14.5cm ) 중|성분명 : 위령선|분량 : 30|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1매 (부직포 및 플라스틱필름 포함 : 7g, 부직포 및 플라스틱필름 제외 : 5g, 10cm x 14.5cm ) 중|성분명 : 목별자|분량 : 15|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1매 (부직포 및 플라스틱필름 포함 : 7g, 부직포 및 플라스틱필름 제외 : 5g, 10cm x 14.5cm ) 중|성분명 : 피마자|분량 : 50|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1매 (부직포 및 플라스틱필름 포함 : 7g, 부직포 및 플라스틱필름 제외 : 5g, 10cm x 14.5cm ) 중|성분명 : 몰약|분량 : 20|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1매 (부직포 및 플라스틱필름 포함 : 7g, 부직포 및 플라스틱필름 제외 : 5g, 10cm x 14.5cm ) 중|성분명 : 유향|분량 : 20|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1매 (부직포 및 플라스틱필름 포함 : 7g, 부직포 및 플라스틱필름 제외 : 5g, 10cm x 14.5cm ) 중|성분명 : L-멘톨|분량 : 40|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1매 (부직포 및 플라스틱필름 포함 : 7g, 부직포 및 플라스틱필름 제외 : 5g, 10cm x 14.5cm ) 중|성분명 : 산화아연|분량 : 50|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1매 (부직포 및 플라스틱필름 포함 : 7g, 부직포 및 플라스틱필름 제외 : 5g, 10cm x 14.5cm ) 중|성분명 : 살리실산메틸|분량 : 10|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1매 (부직포 및 플라스틱필름 포함 : 7g, 부직포 및 플라스틱필름 제외 : 5g, 10cm x 14.5cm ) 중-부직포 및 플라스틱필름 제외 1g 중/1매 (부직포 및 플라스틱필름 포함 : 7g, 부직포 및 플라스틱필름 제외 : 5g, 10cm x 14.5cm ) 중-부직포 및 플라스틱필름', '수집URL': 'https://drug.hospitalk.net/item/200109392', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200109392', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202002620', 'ITEM_NAME': '기넥스타정40밀리그램(은행엽건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은행엽건조엑스', 'ENTP_NAME': '(주)라이트팜텍', 'CHART': '연녹색의 장방형 필름코팅정', 'CHANGE_DATE': '2023-09-07', 'BAR_CODE': '8806456058907,8806456058914,8806456058921,8806903036403,8806903036410,8806903036427,8806971009705,8806971009712,8806971009729', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M088948]은행엽건조엑스', '함량_원료성분원문': '총량 : 1정310밀리그램|성분명 : 은행엽건조엑스|분량 : 40|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1310', '수집URL': 'https://drug.hospitalk.net/item/202002620', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202002620', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202402687', 'ITEM_NAME': '기넥신메모케어캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은행엽 건조엑스;인삼40%에탄올건조엑스', 'ENTP_NAME': '에스케이케미칼(주)', 'CHART': '황갈색의 가루가 들어 있는 오렌지색의 경질캡슐제', 'CHANGE_DATE': '2026-08-07', 'BAR_CODE': '8806447051207,8806447051214', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M273892]은행엽 건조엑스|[M269209]인삼40%에탄올건조엑스', '함량_원료성분원문': '총량 : 1캡슐400밀리그램|성분명 : 인삼40%에탄올건조엑스|분량 : 100|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1캡슐400밀리그램|성분명 : 은행엽 건조엑스|분량 : 60|단위 : 밀리그램|규격 : EP|성분정보 :', '함량_총량기준': '1400', '수집URL': 'https://drug.hospitalk.net/item/202402687', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202402687', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201310515', 'ITEM_NAME': '기넥신에프연질캡슐120밀리그램(은행엽건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은행엽건조엑스', 'ENTP_NAME': '에스케이케미칼(주)', 'CHART': '진한갈색의 내용물이 든 녹색의 타원형 연질캡슐', 'CHANGE_DATE': '2025-12-08', 'BAR_CODE': '8806447041703,8806447041710,8806447041727,8806447041734,8806447041741,8806447041758', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M088948]은행엽건조엑스', '함량_원료성분원문': '총량 : 이 약 1캡슐(610밀리그램) 중|성분명 : 은행엽건조엑스|분량 : 120.0|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '이 약 1캡슐(610밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201310515', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201310515', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202009212', 'ITEM_NAME': '기넥신에프정240밀리그램(은행엽건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은행엽건조엑스', 'ENTP_NAME': '에스케이케미칼(주)', 'CHART': '녹색의 장방형 필름코팅정제', 'CHANGE_DATE': '2023-12-26', 'BAR_CODE': '8806447048405,8806447048412,8806447048429,8806447048436,8806447048443,8806447048450', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M088948]은행엽건조엑스', '함량_원료성분원문': '총량 : 1정730.0밀리그램|성분명 : 은행엽건조엑스|분량 : 240|단위 : 밀리그램|규격 : EP|성분정보 :', '함량_총량기준': '1730.0', '수집URL': 'https://drug.hospitalk.net/item/202009212', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202009212', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199102014', 'ITEM_NAME': '기넥신에프정40밀리그램(은행엽건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은행엽건조엑스', 'ENTP_NAME': '에스케이케미칼(주)', 'CHART': '진녹색의 타원형 필름 코팅정', 'CHANGE_DATE': '2026-01-09', 'BAR_CODE': '8806447001301,8806447001318,8806447001325,8806447001332,8806447001349,8806447001356,8806447001363', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M088948]은행엽건조엑스', '함량_원료성분원문': '총량 : 이 약 1정(253.13 mg) 중|성분명 : 은행엽건조엑스|분량 : 40.0|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '이 약 1정(253.13 mg) 중', '수집URL': 'https://drug.hospitalk.net/item/199102014', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199102014', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200808128', 'ITEM_NAME': '기맥연조엑스(맥문동탕)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '맥문동탕연조엑스(7.1→1)', 'ENTP_NAME': '원광제약(주)', 'CHART': '감미를 가진 암갈색의 연조엑스제', 'CHANGE_DATE': '2017-02-09', 'BAR_CODE': '8806626009203,8806626009210,8806626009227,8806626009234,8806835006406,8806835006413,8806835006420,8806835006437', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M239145]맥문동탕연조엑스(7.1→1)', '함량_원료성분원문': '총량 : 1회용량(7.0g)중|성분명 : 맥문동탕연조엑스(7.1→1)|분량 : 1.5|단위 : 그램|규격 : 별규|성분정보 :', '함량_총량기준': '1회용량(7.0g)중', '수집URL': 'https://drug.hospitalk.net/item/200808128', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200808128', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201507401', 'ITEM_NAME': '기목신정(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '브로멜라인;결정트립신', 'ENTP_NAME': '아주약품(주)', 'CHART': '흰색의 원형 필름코팅정', 'CHANGE_DATE': '2020-03-27', 'BAR_CODE': '8806540047107,8806540047114', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M095415]브로멜라인|[M051649]결정트립신', '함량_원료성분원문': '총량 : 1정293밀리그램|성분명 : 브로멜라인|분량 : 40.0|단위 : 밀리그램|규격 : KP|성분정보 : 20,000브로멜라인단위;총량 : 1정293밀리그램|성분명 : 결정트립신|분량 : 1.0|단위 : 밀리그램|규격 : USP|성분정보 : 2,500USP트립신단위', '함량_총량기준': '1293', '수집URL': 'https://drug.hospitalk.net/item/201507401', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201507401', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201900101', 'ITEM_NAME': '깅고맥스정80밀리그램(은행엽건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은행엽건조엑스', 'ENTP_NAME': '(주)메디카코리아', 'CHART': '녹색의 장방형 필름코팅정', 'CHANGE_DATE': '2020-07-23', 'BAR_CODE': '8806460045207,8806460045214,8806460045221,8806460045238', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M088948]은행엽건조엑스', '함량_원료성분원문': '총량 : 이 약 1정(462.0mg)중|성분명 : 은행엽건조엑스|분량 : 80.0|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '이 약 1정(462.0mg)중', '수집URL': 'https://drug.hospitalk.net/item/201900101', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201900101', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202402106', 'ITEM_NAME': '깅코라민정240밀리그램(은행엽건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은행엽 건조엑스', 'ENTP_NAME': '(주)마더스제약', 'CHART': '녹색의 장방형 필름코팅정제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806228053901,8806228053918,8806228053925', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M273892]은행엽 건조엑스', '함량_원료성분원문': '총량 : 1정730.0밀리그램|성분명 : 은행엽 건조엑스|분량 : 240|단위 : 밀리그램|규격 : EP|성분정보 :', '함량_총량기준': '1730.0', '수집URL': 'https://drug.hospitalk.net/item/202402106', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202402106', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201503790', 'ITEM_NAME': '깅코라민정80밀리그램(은행엽건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은행엽건조엑스', 'ENTP_NAME': '(주)마더스제약', 'CHART': '녹색의 원형 필름코팅정', 'CHANGE_DATE': '2026-03-16', 'BAR_CODE': '8806228039707,8806228039714,8806228039721,8806228039738', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M088948]은행엽건조엑스', '함량_원료성분원문': '총량 : 1정250밀리그램|성분명 : 은행엽건조엑스|분량 : 80.0|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1250', '수집URL': 'https://drug.hospitalk.net/item/201503790', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201503790', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199900216', 'ITEM_NAME': '까스명수에프액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '창출;육두구;건강;정향;육계;현호색;고추틴크;L-멘톨;후박;진피;아선약', 'ENTP_NAME': '삼성제약(주)', 'CHART': '이산화탄소가 포화된 적갈색의 액제', 'CHANGE_DATE': '2022-11-29', 'BAR_CODE': '8806423001202,8806423001219,8806423086902,8806423086919,8806473041708,8806473041715', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040548]창출|[M040486]육두구|[M040007]건강|[M040527]정향|[M050036]육계|[M040775]현호색|[M070048]고추틴크|[M279284]L-멘톨|[M040813]후박|[M040538]진피|[M040350]아선약', '함량_원료성분원문': '총량 : 1병(75mL) 중|성분명 : 아선약|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL) 중|성분명 : 진피|분량 : 250|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL) 중|성분명 : 후박|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL) 중|성분명 : L-멘톨|분량 : 16|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL) 중|성분명 : 고추틴크|분량 : 0.06|단위 : 밀리리터|규격 : KP|성분정보 : ;총량 : 1병(75mL) 중|성분명 : 현호색|분량 : 180|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL) 중|성분명 : 육계|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL) 중|성분명 : 정향|분량 : 12|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL) 중|성분명 : 건강|분량 : 12|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL) 중|성분명 : 육두구|분량 : 6|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL) 중|성분명 : 창출|분량 : 3|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1병(75mL) 중', '수집URL': 'https://drug.hospitalk.net/item/199900216', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199900216', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201508272', 'ITEM_NAME': '까스앤프리츄정80밀리그램(시메티콘)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시메티콘', 'ENTP_NAME': '한미약품(주)', 'CHART': '흰색의 씹어먹는 원형 정제', 'CHANGE_DATE': '2022-12-16', 'BAR_CODE': '8806435074805,8806435074812', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223083]시메티콘', '함량_원료성분원문': '총량 : 1정 (1,052mg) 중|성분명 : 시메티콘|분량 : 80|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1정 (1,052mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201508272', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201508272', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200300531', 'ITEM_NAME': '까스활명수디액(수출명:까스활명수큐)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '육두구;건강;계피;아선약;정향;현호색;엘 멘톨;고추틴크;창출', 'ENTP_NAME': '동화약품(주)', 'CHART': '이산화탄소가 포화된 적갈색의 액제이다.', 'CHANGE_DATE': '2019-06-20', 'BAR_CODE': '8806427000706,8806427000713', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040486]육두구|[M040007]건강|[M040016]계피|[M040350]아선약|[M040527]정향|[M040775]현호색|[M219244]엘 멘톨|[M070048]고추틴크|[M040548]창출', '함량_원료성분원문': '총량 : 1병 중 75밀리리터|성분명 : 육두구|분량 : 6|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병 중 75밀리리터|성분명 : 창출|분량 : 3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병 중 75밀리리터|성분명 : 고추틴크|분량 : 0.06|단위 : 밀리리터|규격 : KP|성분정보 : ;총량 : 1병 중 75밀리리터|성분명 : 엘 멘톨|분량 : 16|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병 중 75밀리리터|성분명 : 현호색|분량 : 90|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병 중 75밀리리터|성분명 : 정향|분량 : 12|단위 : 밀리그램|규격 : KP|성분정보 : 오이게놀로서 1.3mg;총량 : 1병 중 75밀리리터|성분명 : 아선약|분량 : 100|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병 중 75밀리리터|성분명 : 계피|분량 : 30|단위 : 밀리그램|규격 : KP|성분정보 : 계피산으로서 9㎍;총량 : 1병 중 75밀리리터|성분명 : 건강|분량 : 12|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1병 중 75밀리리터', '수집URL': 'https://drug.hospitalk.net/item/200300531', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200300531', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201110738', 'ITEM_NAME': '까스활명수액(Gas Whal Myung Su) (수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '진피, 후박, 현호색, 아선약 70% 에탄올연조엑스(3→1);창출;육두구;건강;정향;육계;고추틴크;L-멘톨', 'ENTP_NAME': '동화약품(주)', 'CHART': '적갈색의 불투명한 액제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806427059001,8806427059018', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M253597]진피, 후박, 현호색, 아선약 70% 에탄올연조엑스(3→1)|[M040548]창출|[M040486]육두구|[M040007]건강|[M040527]정향|[M050036]육계|[M070048]고추틴크|[M279284]L-멘톨', '함량_원료성분원문': '총량 : 1병(75mL)중|성분명 : L-멘톨|분량 : 3.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL)중|성분명 : 고추틴크|분량 : 0.07|단위 : 밀리리터|규격 : KP|성분정보 : ;총량 : 1병(75mL)중|성분명 : 육계|분량 : 30.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL)중|성분명 : 정향|분량 : 12.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL)중|성분명 : 건강|분량 : 12.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL)중|성분명 : 육두구|분량 : 6.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL)중|성분명 : 창출|분량 : 3.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL)중|성분명 : 진피, 후박, 현호색, 아선약 70% 에탄올연조엑스(3→1)|분량 : 193.33|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : (진피 250mg, 후박 50mg, 현호색 180mg, 아선약 100mg)', '함량_총량기준': '1병(75mL)중', '수집URL': 'https://drug.hospitalk.net/item/201110738', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201110738', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198900667', 'ITEM_NAME': '까스활명수큐액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '육두구;건강;정향;육계;현호색;고추틴크;진피;L-멘톨;창출;후박;아선약', 'ENTP_NAME': '동화약품(주)', 'CHART': '이산화탄소가 포화된 적갈색의 액제', 'CHANGE_DATE': '2022-11-02', 'BAR_CODE': '8806427000904,8806427000911', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040486]육두구|[M040007]건강|[M040527]정향|[M050036]육계|[M040775]현호색|[M070048]고추틴크|[M040538]진피|[M279284]L-멘톨|[M040548]창출|[M040813]후박|[M040350]아선약', '함량_원료성분원문': '총량 : 1병75밀리리터|성분명 : 아선약|분량 : 100.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병75밀리리터|성분명 : 후박|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병75밀리리터|성분명 : 창출|분량 : 3.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병75밀리리터|성분명 : L-멘톨|분량 : 16.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병75밀리리터|성분명 : 진피|분량 : 250.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병75밀리리터|성분명 : 고추틴크|분량 : 0.06|단위 : 밀리리터|규격 : KP|성분정보 : ;총량 : 1병75밀리리터|성분명 : 현호색|분량 : 180.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병75밀리리터|성분명 : 육계|분량 : 30.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병75밀리리터|성분명 : 정향|분량 : 12.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병75밀리리터|성분명 : 건강|분량 : 12.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병75밀리리터|성분명 : 육두구|분량 : 6.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '175', '수집URL': 'https://drug.hospitalk.net/item/198900667', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198900667', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201601802', 'ITEM_NAME': '꼬마활명수액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '오매;아선약;현호색;후박;진피;육두구;건강;정향;육계', 'ENTP_NAME': '동화약품(주)', 'CHART': '갈색의 액제', 'CHANGE_DATE': '2025-09-10', 'BAR_CODE': '8806427064005,8806427064012,8806427064029,8806427064036,8806427064043', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051152]오매|[M040350]아선약|[M040775]현호색|[M040813]후박|[M040538]진피|[M040486]육두구|[M040007]건강|[M040527]정향|[M050036]육계', '함량_원료성분원문': '총량 : 100 mL 중|성분명 : 육계|분량 : 270|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100 mL 중|성분명 : 정향|분량 : 108|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100 mL 중|성분명 : 건강|분량 : 108|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100 mL 중|성분명 : 육두구|분량 : 54|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100 mL 중|성분명 : 진피|분량 : 1666.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100 mL 중|성분명 : 후박|분량 : 333.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100 mL 중|성분명 : 현호색|분량 : 1200|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100 mL 중|성분명 : 아선약|분량 : 666.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100 mL 중|성분명 : 오매|분량 : 2233|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '100 mL 중', '수집URL': 'https://drug.hospitalk.net/item/201601802', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201601802', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202200088', 'ITEM_NAME': '나나정500밀리그램(아세트아미노펜)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아세트아미노펜', 'ENTP_NAME': '초당약품공업(주)', 'CHART': '흰색의 장방형 필름코팅정제', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806707020202,8806707020219,8806707020226,8806707020233,8806707020240', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040353]아세트아미노펜|[M040353]아세트아미노펜', '함량_원료성분원문': '총량 : 1정645.0밀리그램|성분명 : 아세트아미노펜|분량 : 500.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정645.0밀리그램|성분명 : 아세트아미노펜|분량 : 500.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1645.0/1645.0', '수집URL': 'https://drug.hospitalk.net/item/202200088', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202200088', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202002089', 'ITEM_NAME': '나노디오정600밀리그램(디오스민)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '디오스민', 'ENTP_NAME': '초당약품공업(주)', 'CHART': '연두색의 원형 필름코팅정제', 'CHANGE_DATE': '2021-11-01', 'BAR_CODE': '8806707019701,8806707019718,8806707019725,8806707019732,8806707019749', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M082272]디오스민', '함량_원료성분원문': '총량 : 1정970밀리그램|성분명 : 디오스민|분량 : 600|단위 : 밀리그램|규격 : EP|성분정보 :', '함량_총량기준': '1970', '수집URL': 'https://drug.hospitalk.net/item/202002089', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202002089', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200904182', 'ITEM_NAME': '나노민연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아스코르브산;시아노코발라민;리보플라빈;티아민질산염;농축콜레칼시페롤유;레티놀팔미테이트', 'ENTP_NAME': '한솔신약(주)', 'CHART': '미황색의 내용물을 함유한 암갈색의 장방형 연질캡슐', 'CHANGE_DATE': '2021-08-10', 'BAR_CODE': '8806458017001,8806458017018,8806458017025,8806458017032', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M258994]아스코르브산|[M096429]시아노코발라민|[M040133]리보플라빈|[M223262]티아민질산염|[M245627]농축콜레칼시페롤유|[M222991]레티놀팔미테이트', '함량_원료성분원문': '총량 : 1캡슐(1,020밀리그램) 중|성분명 : 레티놀팔미테이트|분량 : 0.588|단위 : 밀리그램|규격 : KP|성분정보 : 비타민A로서 1,000IU;총량 : 1캡슐(1,020밀리그램) 중|성분명 : 농축콜레칼시페롤유|분량 : 100.00|단위 : 마이크로그램|규격 : BP|성분정보 : 비타민D로서 100IU;총량 : 1캡슐(1,020밀리그램) 중|성분명 : 티아민질산염|분량 : 10.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,020밀리그램) 중|성분명 : 리보플라빈|분량 : 4.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,020밀리그램) 중|성분명 : 시아노코발라민|분량 : 6.00|단위 : 마이크로그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,020밀리그램) 중|성분명 : 아스코르브산|분량 : 20.00|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1캡슐(1,020밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200904182', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200904182', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202201153', 'ITEM_NAME': '나노파모정10밀리그램(파모티딘)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '파모티딘', 'ENTP_NAME': '초당약품공업(주)', 'CHART': '연녹색의 원형 필름코팅정', 'CHANGE_DATE': '2024-11-07', 'BAR_CODE': '8806707020301,8806707020318,8806707020325,8806707020332', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081653]파모티딘', '함량_원료성분원문': '총량 : 1정|성분명 : 파모티딘|분량 : 10.0|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/202201153', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202201153', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200404626', 'ITEM_NAME': '나녹시딜액5%(미녹시딜)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '미녹시딜', 'ENTP_NAME': '(주)나노팜', 'CHART': '플라스틱용기에 든 무색 또는 엷은 황색의 투명한 액체', 'CHANGE_DATE': '2026-03-10', 'BAR_CODE': '8806589000309,8806589000316,8806589000323,8806589000330,8806589000347', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081480]미녹시딜', '함량_원료성분원문': '총량 : 100mL 중|성분명 : 미녹시딜|분량 : 5|단위 : 그램|규격 : USP|성분정보 :', '함량_총량기준': '100mL 중', '수집URL': 'https://drug.hospitalk.net/item/200404626', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200404626', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199800354', 'ITEM_NAME': '나니실크림(테르비나핀염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '테르비나핀염산염', 'ENTP_NAME': '(주)에이프로젠바이오로직스', 'CHART': '흰색의 크림제', 'CHANGE_DATE': '2020-09-01', 'BAR_CODE': '8806452042900,8806452042917,8806452042924,8806452042931,8806518001100,8806518001117,8806518001124,8806518001131', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M245869]테르비나핀염산염', '함량_원료성분원문': '총량 : 1g 중|성분명 : 테르비나핀염산염|분량 : 10|단위 : 밀리그램|규격 : JP|성분정보 : 테르비나핀으로서 8.888mg', '함량_총량기준': '1g 중', '수집URL': 'https://drug.hospitalk.net/item/199800354', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199800354', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202602236', 'ITEM_NAME': '나니카크림(테르비나핀염산염)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '테르비나핀염산염', 'ENTP_NAME': '(주)에이프로젠바이오로직스', 'CHART': '백색의 크림제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '미기재', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M258362]테르비나핀염산염', '함량_원료성분원문': '총량 : 이 약 1그램 중|성분명 : 테르비나핀염산염|분량 : 10|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '이 약 1그램 중', '수집URL': 'https://drug.hospitalk.net/item/202602236', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202602236', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200201190', 'ITEM_NAME': '나덴정(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아르기닌;이부프로펜', 'ENTP_NAME': '(주)다림바이오텍', 'CHART': '분홍색의 장방형 필름코팅정', 'CHANGE_DATE': '2024-07-15', 'BAR_CODE': '8806646000907', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M095195]아르기닌|[M051259]이부프로펜', '함량_원료성분원문': '총량 : 1정648밀리그램|성분명 : 이부프로펜|분량 : 200.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정648밀리그램|성분명 : 아르기닌|분량 : 185.0|단위 : 밀리그램|규격 : BP|성분정보 :', '함량_총량기준': '1648', '수집URL': 'https://drug.hospitalk.net/item/200201190', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200201190', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202600160', 'ITEM_NAME': '나드정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '토코페롤아세테이트 2배산;레티놀팔미테이트;니코틴산아미드;니코틴산', 'ENTP_NAME': '(주)킵스바이오파마', 'CHART': '흰색의 장방형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806932027403,8806932027410,8806932027427', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M255819]토코페롤아세테이트 2배산|[M222991]레티놀팔미테이트|[M040064]니코틴산아미드|[M040063]니코틴산', '함량_원료성분원문': '총량 : 1정595.58밀리그램|성분명 : 니코틴산|분량 : 30|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1정595.58밀리그램|성분명 : 니코틴산아미드|분량 : 220|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정595.58밀리그램|성분명 : 레티놀팔미테이트|분량 : 1.18|단위 : 밀리그램|규격 : USP|성분정보 : 비타민A로서(으)로서 2000 아이.유;총량 : 1정595.58밀리그램|성분명 : 토코페롤아세테이트 2배산|분량 : 200|단위 : 밀리그램|규격 : KP|성분정보 : 비타민E(으)로서 100 아이.유', '함량_총량기준': '1595.58', '수집URL': 'https://drug.hospitalk.net/item/202600160', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202600160', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202400578', 'ITEM_NAME': '나들이시럽', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '피리독신염산염;디멘히드리네이트;카페인무수물', 'ENTP_NAME': '(주)이든파마', 'CHART': '알루미늄스틱포에 충전된 무색 또는 미황색의 시럽제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806289023806,8806289023813,8806289023820', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M204304]피리독신염산염|[M040096]디멘히드리네이트|[M223183]카페인무수물', '함량_원료성분원문': '총량 : 1포10밀리리터|성분명 : 카페인무수물|분량 : 16.67|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포10밀리리터|성분명 : 디멘히드리네이트|분량 : 33.33|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포10밀리리터|성분명 : 피리독신염산염|분량 : 4.17|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '110', '수집URL': 'https://drug.hospitalk.net/item/202400578', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202400578', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200607905', 'ITEM_NAME': '나록펜정(나프록센나트륨)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '나프록센나트륨', 'ENTP_NAME': '한국유니온제약(주)', 'CHART': '백색-미백색의 장방형 필름코팅정제', 'CHANGE_DATE': '2024-12-12', 'BAR_CODE': '8806655000509', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M070724]나프록센나트륨', '함량_원료성분원문': '총량 : 373mg|성분명 : 나프록센나트륨|분량 : 275|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '373mg-1정', '수집URL': 'https://drug.hospitalk.net/item/200607905', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200607905', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200000934', 'ITEM_NAME': '나르신캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '다엽가루;오르소시폰가루', 'ENTP_NAME': '(주)바이넥스', 'CHART': '녹색 분말의 내용물이 든 상부 암녹색의 불투명, 하부 미황색의 경질캡슐제.', 'CHANGE_DATE': '2025-05-26', 'BAR_CODE': '8806431000105,8806431000112,8806431000129', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M098431]다엽가루|[M100027]오르소시폰가루', '함량_원료성분원문': '총량 : 1캡슐504밀리그램|성분명 : 다엽가루|분량 : 250|단위 : 밀리그램|규격 : 생규|성분정보 : Caffeine으로서 5mg;총량 : 1캡슐504밀리그램|성분명 : 오르소시폰가루|분량 : 150|단위 : 밀리그램|규격 : 생규|성분정보 : Sinensetin으로서 0.07mg', '함량_총량기준': '1504', '수집URL': 'https://drug.hospitalk.net/item/200000934', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200000934', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198900833', 'ITEM_NAME': '나리스타에스점비액(수출명:듀라존점비액,나소존점비액)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '나파졸린염산염;클로르페니라민말레산염;글리시리진산이칼륨', 'ENTP_NAME': '삼천당제약(주)', 'CHART': '특이한 방향성이 있는 무색투명한 액체', 'CHANGE_DATE': '2026-09-09', 'BAR_CODE': '8806512000505,8806512000512', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M222937]나파졸린염산염|[M223211]클로르페니라민말레산염|[M256386]글리시리진산이칼륨', '함량_원료성분원문': '총량 : 100mL 중|성분명 : 나파졸린염산염|분량 : 50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100mL 중|성분명 : 클로르페니라민말레산염|분량 : 250|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100mL 중|성분명 : 글리시리진산이칼륨|분량 : 300|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '100mL 중', '수집URL': 'https://drug.hospitalk.net/item/198900833', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198900833', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201502828', 'ITEM_NAME': '나리스타자일로점비액(자일로메타졸린염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '자일로메타졸린염산염', 'ENTP_NAME': '삼천당제약(주)', 'CHART': '무색 내지 연한 노란색의 투명한 액제', 'CHANGE_DATE': '2024-07-29', 'BAR_CODE': '8806512043007,8806512043014,8806512043021', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M257887]자일로메타졸린염산염', '함량_원료성분원문': '총량 : 1밀리리터|성분명 : 자일로메타졸린염산염|분량 : 1|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/201502828', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201502828', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199802633', 'ITEM_NAME': '나미진크림(테르비나핀염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '테르비나핀염산염', 'ENTP_NAME': '(주)씨엠지제약', 'CHART': '흰색의 크림제', 'CHANGE_DATE': '2024-09-02', 'BAR_CODE': '8806486000501,8806486000518,8806486000525,8806486000532', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M258362]테르비나핀염산염', '함량_원료성분원문': '총량 : 1그램|성분명 : 테르비나핀염산염|분량 : 10|단위 : 밀리그램|규격 : JP|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/199802633', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199802633', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199900298', 'ITEM_NAME': '나바론크림(디클로페낙디에틸암모늄)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '디클로페낙디에틸암모늄', 'ENTP_NAME': '(주)에이프로젠바이오로직스', 'CHART': '흰색 연질의 균질한 크림제', 'CHANGE_DATE': '2024-12-12', 'BAR_CODE': '8806452052107,8806452052114,8806452052121,8806518001209', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M249599]디클로페낙디에틸암모늄', '함량_원료성분원문': '총량 : 1g중|성분명 : 디클로페낙디에틸암모늄|분량 : 11.6|단위 : 밀리그램|규격 : KP|성분정보 : 디클로페낙으로서 10밀리그램', '함량_총량기준': '1g중', '수집URL': 'https://drug.hospitalk.net/item/199900298', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199900298', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199604593', 'ITEM_NAME': '나박점안액(엔-아세틸아스파틸글루타민산나트륨)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '엔-아세틸아스파틸글루타민산나트륨', 'ENTP_NAME': '삼일제약(주)', 'CHART': '흰색의 불투명한 아박(ABAK FS)용기에 들어있는 보존제가 없는 무색, 투명한 무취의 점안액', 'CHANGE_DATE': '2019-06-21', 'BAR_CODE': '8806439000503,8806439000510,8806439000527', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M269811]엔-아세틸아스파틸글루타민산나트륨', '함량_원료성분원문': '총량 : 1밀리리터 중|성분명 : 엔-아세틸아스파틸글루타민산나트륨|분량 : 49|단위 : 밀리그램|규격 : 별규|성분정보 : 무수물로서', '함량_총량기준': '1밀리리터 중', '수집URL': 'https://drug.hospitalk.net/item/199604593', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199604593', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201707455', 'ITEM_NAME': '나스타제정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '디아스타제·프로테아제·셀룰라제;리파제;우르소데옥시콜산;시메티콘파우더', 'ENTP_NAME': '(주)한국파마', 'CHART': '녹색의 장방형 필름코팅정제', 'CHANGE_DATE': '2020-02-14', 'BAR_CODE': '8806530059608,8806530059615,8806530059622,8806530059646', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M267745]디아스타제·프로테아제·셀룰라제|[M050379]리파제|[M223167]우르소데옥시콜산|[M270842]시메티콘파우더', '함량_원료성분원문': '총량 : 1정451.25밀리그램|성분명 : 디아스타제·프로테아제·셀룰라제|분량 : 20|단위 : 밀리그램|규격 : KP|성분정보 : 전분당화력(pH4.5)278단위이상, 전분호정화력(pH4.5)640단위이상, 단백소화력(pH3.0)170단위이상, 섬유소당화력(pH4.5)2단위이상;총량 : 1정451.25밀리그램|성분명 : 리파제|분량 : 20|단위 : 밀리그램|규격 : KP|성분정보 : 지방소화력(pH6.0)120단위;총량 : 1정451.25밀리그램|성분명 : 우르소데옥시콜산|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정451.25밀리그램|성분명 : 시메티콘파우더|분량 : 46.15|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : 시메티콘(으)로서 30 밀리그램', '함량_총량기준': '1451.25', '수집URL': 'https://drug.hospitalk.net/item/201707455', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201707455', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202200195', 'ITEM_NAME': '나스펜시럽(아세트아미노펜)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아세트아미노펜', 'ENTP_NAME': '조아제약(주)', 'CHART': '흰색 내지 연한 노란색의 체리향 액이 알루미늄 호일 파우치에 든 현탁성 시럽제', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806446043401,8806446043418,8806446043425', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040353]아세트아미노펜', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 아세트아미노펜|분량 : 3.200|단위 : 그램|규격 : USP|성분정보 :', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/202200195', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202200195', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201306491', 'ITEM_NAME': '나쎈연질캡슐(나프록센)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '나프록센', 'ENTP_NAME': '신일제약(주)', 'CHART': '미황 내지 연한 녹색의 내용물을 함유한 녹색 투명의 타원형 연질캡슐제', 'CHANGE_DATE': '2026-08-21', 'BAR_CODE': '8806538048109,8806538048116', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050116]나프록센', '함량_원료성분원문': '총량 : 1캡슐(971mg)중|성분명 : 나프록센|분량 : 250|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1캡슐(971mg)중', '수집URL': 'https://drug.hospitalk.net/item/201306491', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201306491', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201309340', 'ITEM_NAME': '나오덤크림(구아야줄렌)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '구아야줄렌', 'ENTP_NAME': '신신제약(주)', 'CHART': '엷은 청색의 크림제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806438021301,8806438021318,8806438021325,8806438021332', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256451]구아야줄렌', '함량_원료성분원문': '총량 : 이 약 1g 중|성분명 : 구아야줄렌|분량 : 0.33|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 1g 중', '수집URL': 'https://drug.hospitalk.net/item/201309340', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201309340', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200810499', 'ITEM_NAME': '나오미정(방기황기탕건조엑스 7.52→1)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '방기황기탕건조엑스(7.52→1)', 'ENTP_NAME': '대한뉴팜(주)', 'CHART': '연녹색의 원형 필름코팅정제', 'CHANGE_DATE': '2018-12-19', 'BAR_CODE': '8806699053103,8806699053110', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M211366]방기황기탕건조엑스(7.52→1)', '함량_원료성분원문': '총량 : 1정380.7밀리그램|성분명 : 방기황기탕건조엑스(7.52→1)|분량 : 244|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1380.7', '수집URL': 'https://drug.hospitalk.net/item/200810499', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200810499', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202601253', 'ITEM_NAME': '나우씨펜정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '카페인무수물;아세트아미노펜', 'ENTP_NAME': '(주)다산제약', 'CHART': '흰색의 장방형 정제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806786023606,8806786023613', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223183]카페인무수물|[M040353]아세트아미노펜', '함량_원료성분원문': '총량 : 1정700.00|성분명 : 아세트아미노펜|분량 : 500.00|단위 : 밀리그램|규격 : EP|성분정보 : ;총량 : 1정700.00|성분명 : 카페인무수물|분량 : 20.00|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1700.00', '수집URL': 'https://drug.hospitalk.net/item/202601253', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202601253', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200002316', 'ITEM_NAME': '나이스과립', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '차전자피;센나열매', 'ENTP_NAME': '오스틴제약(주)', 'CHART': '갈색의 과립제', 'CHANGE_DATE': '2021-01-26', 'BAR_CODE': '8806543001106,8806543001113,8806543001120,8806543001137,8806543001144', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081198]차전자피|[M050805]센나열매', '함량_원료성분원문': '총량 : 1포(4.0g) 중|성분명 : 차전자피|분량 : 2168|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1포(4.0g) 중|성분명 : 센나열매|분량 : 496|단위 : 밀리그램|규격 : BP|성분정보 : 센노사이드 B로서 10.9mg', '함량_총량기준': '1포(4.0g) 중', '수집URL': 'https://drug.hospitalk.net/item/200002316', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200002316', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202600328', 'ITEM_NAME': '나이아미정(니코틴산아미드)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '니코틴산아미드', 'ENTP_NAME': '경남제약(주)', 'CHART': '주황색의 타원형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806476041507,8806476041514', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040064]니코틴산아미드', '함량_원료성분원문': '총량 : 1정643.3밀리그램|성분명 : 니코틴산아미드|분량 : 500|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1643.3', '수집URL': 'https://drug.hospitalk.net/item/202600328', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202600328', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201602427', 'ITEM_NAME': '나인나인정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아스코르브산97%과립;산화마그네슘;황산칼륨;우르소데옥시콜산;콜린타르타르산염;오로트산수화물;염화크롬수화물;요오드화칼륨;몰리브덴산나트륨;폴산;레티놀아세테이트;피토나디온 5%;리보플라빈;푸마르산철;셀레늄가루 0.1%;무수인산수소칼슘;베타카로틴20%과립;티아민질산염;피리독신염산염;비오틴;콜레칼시페롤과립;황산제이구리수화물;황산망간;판토텐산칼슘;산화아연;니코틴산아미드;시아노코발라민1000배산;토코페롤아세테이트 2배산', 'ENTP_NAME': '한미약품(주)', 'CHART': '흐린 빨간 갈색의 타원형 필름코팅정', 'CHANGE_DATE': '2026-03-20', 'BAR_CODE': '8806435075505,8806435075512', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M227509]아스코르브산97%과립|[M040262]산화마그네슘|[M040806]황산칼륨|[M223167]우르소데옥시콜산|[M247683]콜린타르타르산염|[M250837]오로트산수화물|[M250274]염화크롬수화물|[M040473]요오드화칼륨|[M050494]몰리브덴산나트륨|[M223289]폴산|[M205408]레티놀아세테이트|[M228553]피토나디온 5%|[M040133]리보플라빈|[M051783]푸마르산철|[M248796]셀레늄가루 0.1%|[M091374]무수인산수소칼슘|[M086546]베타카로틴20%과립|[M223262]티아민질산염|[M204304]피리독신염산염|[M050704]비오틴|[M099907]콜레칼시페롤과립|[M247355]황산제이구리수화물|[M051962]황산망간|[M244748]판토텐산칼슘|[M243785]산화아연|[M040064]니코틴산아미드|[M255994]시아노코발라민1000배산|[M255819]토코페롤아세테이트 2배산', '함량_원료성분원문': '총량 : 1정1251.75밀리그램|성분명 : 무수인산수소칼슘|분량 : 421.54|단위 : 밀리그램|규격 : USP|성분정보 : 칼슘으로서 124.175mg, 총 인으로서96mg;총량 : 1정1251.75밀리그램|성분명 : 베타카로틴20%과립|분량 : 3.6|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : 베타카로틴으로서 0.72mg;총량 : 1정1251.75밀리그램|성분명 : 티아민질산염|분량 : 2.775|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정1251.75밀리그램|성분명 : 피리독신염산염|분량 : 4.02|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정1251.75밀리그램|성분명 : 비오틴|분량 : 0.06|단위 : 밀리그램|규격 : USP|성분정보 : 비오틴으로서 60㎍;총량 : 1정1251.75밀리그램|성분명 : 콜레칼시페롤과립|분량 : 7.5|단위 : 밀리그램|규격 : EP|성분정보 : 비타민D로서 750IU;총량 : 1정1251.75밀리그램|성분명 : 황산제이구리수화물|분량 : 1.76|단위 : 밀리그램|규격 : USP|성분정보 : 구리로서 0.45mg;총량 : 1정1251.75밀리그램|성분명 : 황산망간|분량 : 7.69|단위 : 밀리그램|규격 : EP|성분정보 : 망간으로서 2.5mg;총량 : 1정1251.75밀리그램|성분명 : 판토텐산칼슘|분량 : 9.813|단위 : 밀리그램|규격 : KP|성분정보 : 판토텐산으로서 9mg,칼슘으로서 0.825mg;총량 : 1정1251.75밀리그램|성분명 : 산화아연|분량 : 9.33|단위 : 밀리그램|규격 : KP|성분정보 : 아연으로서 7.5mg;총량 : 1정1251.75밀리그램|성분명 : 니코틴산아미드|분량 : 27|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정1251.75밀리그램|성분명 : 시아노코발라민1000배산|분량 : 6|단위 : 밀리그램|규격 : KP|성분정보 : 시아노코발라민으로서 6㎍;총량 : 1정1251.75밀리그램|성분명 : 토코페롤아세테이트 2배산|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : 비타민E로서 30IU;총량 : 1정1251.75밀리그램|성분명 : 셀레늄가루 0.1%|분량 : 29.5|단위 : 밀리그램|규격 : KP|성분정보 : 셀레늄으로서 29.5㎍;총량 : 1정1251.75밀리그램|성분명 : 푸마르산철|분량 : 54.76|단위 : 밀리그램|규격 : KP|성분정보 : 철로서 18mg;총량 : 1정1251.75밀리그램|성분명 : 아스코르브산97%과립|분량 : 61.85|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : 아스코르브산으로서 60mg;총량 : 1정1251.75밀리그램|성분명 : 산화마그네슘|분량 : 82.92|단위 : 밀리그램|규격 : USP|성분정보 : 마그네슘으로서 50mg;총량 : 1정1251.75밀리그램|성분명 : 황산칼륨|분량 : 89.15|단위 : 밀리그램|규격 : KP|성분정보 : 칼륨으로서 40mg;총량 : 1정1251.75밀리그램|성분명 : 우르소데옥시콜산|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정1251.75밀리그램|성분명 : 콜린타르타르산염|분량 : 10|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1정1251.75밀리그램|성분명 : 오로트산수화물|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정1251.75밀리그램|성분명 : 염화크롬수화물|분량 : 0.102|단위 : 밀리그램|규격 : USP|성분정보 : 크롬으로서 20㎍;총량 : 1정1251.75밀리그램|성분명 : 요오드화칼륨|분량 : 0.098|단위 : 밀리그램|규격 : USP|성분정보 : 요오드로서 75㎍;총량 : 1정1251.75밀리그램|성분명 : 몰리브덴산나트륨|분량 : 0.051|단위 : 밀리그램|규격 : EP|성분정보 : 몰리브덴으로서 20㎍;총량 : 1정1251.75밀리그램|성분명 : 폴산|분량 : 0.4|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정1251.75밀리그램|성분명 : 레티놀아세테이트|분량 : 1.8|단위 : 밀리그램|규격 : EP|성분정보 : 비타민A로서 900IU;총량 : 1정1251.75밀리그램|성분명 : 피토나디온 5%|분량 : 1.95|단위 : 밀리그램|규격 : 별첨규격(전과동)|성분정보 : 비타민 K로서 97.5㎍;총량 : 1정1251.75밀리그램|성분명 : 리보플라빈|분량 : 2.4|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '11251.75', '수집URL': 'https://drug.hospitalk.net/item/201602427', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201602427', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199202073', 'ITEM_NAME': '나졸액(케토코나졸)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '케토코나졸', 'ENTP_NAME': '한미약품(주)', 'CHART': '점성이 있는 분홍색의 액제이다.', 'CHANGE_DATE': '2021-05-24', 'BAR_CODE': '8806435001702,8806435001719,8806435001726,8806435001733,8806435001740', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M080618]케토코나졸', '함량_원료성분원문': '총량 : 100그램|성분명 : 케토코나졸|분량 : 2|단위 : 그램|규격 : USP|성분정보 :', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/199202073', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199202073', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199500319', 'ITEM_NAME': '나콜플러스시럽', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아세트아미노펜;클로르페니라민말레산염;티페피딘시트르산염;dl-메틸에페드린염산염;카페인수화물', 'ENTP_NAME': '일동제약(주)', 'CHART': '갈색 유리병에 든 포도향이 나는 무색 내지 엷은 황색의 맑은 시럽제', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806429000407,8806429000414,8806429000421', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040353]아세트아미노펜|[M223211]클로르페니라민말레산염|[M254445]티페피딘시트르산염|[M204422]dl-메틸에페드린염산염|[M223184]카페인수화물', '함량_원료성분원문': '총량 : 100밀리리터 중|성분명 : 아세트아미노펜|분량 : 1000.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터 중|성분명 : 클로르페니라민말레산염|분량 : 8.3|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 100밀리리터 중|성분명 : 티페피딘시트르산염|분량 : 66.6|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터 중|성분명 : dl-메틸에페드린염산염|분량 : 83.3|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 100밀리리터 중|성분명 : 카페인수화물|분량 : 83.3|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '100밀리리터 중', '수집URL': 'https://drug.hospitalk.net/item/199500319', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199500319', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202107510', 'ITEM_NAME': '나트콜연질캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '덱스트로메토르판브롬화수소산염수화물;리보플라빈;클로르페니라민말레산염;슈도에페드린염산염;구아이페네신;dl-메틸에페드린염산염;아세트아미노펜', 'ENTP_NAME': '(주)서흥', 'CHART': '노란색의 내용물을 함유한 노란색의 타원형 연질캡슐', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806796014601,8806796014618', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M222957]덱스트로메토르판브롬화수소산염수화물|[M040133]리보플라빈|[M223211]클로르페니라민말레산염|[M203364]슈도에페드린염산염|[M050058]구아이페네신|[M204422]dl-메틸에페드린염산염|[M040353]아세트아미노펜', '함량_원료성분원문': '총량 : 1캡슐790밀리그램|성분명 : 아세트아미노펜|분량 : 180|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐790밀리그램|성분명 : dl-메틸에페드린염산염|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐790밀리그램|성분명 : 구아이페네신|분량 : 20.84|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐790밀리그램|성분명 : 슈도에페드린염산염|분량 : 15|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1캡슐790밀리그램|성분명 : 클로르페니라민말레산염|분량 : 1.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐790밀리그램|성분명 : 리보플라빈|분량 : 2|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐790밀리그램|성분명 : 덱스트로메토르판브롬화수소산염수화물|분량 : 8|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1790', '수집URL': 'https://drug.hospitalk.net/item/202107510', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202107510', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201605527', 'ITEM_NAME': '나프날크림(나프티핀염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '나프티핀염산염', 'ENTP_NAME': '풍림무약(주)', 'CHART': '흰색의 크림제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806490016000,8806490016017', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M253457]나프티핀염산염', '함량_원료성분원문': '총량 : 이 약 1그램 중|성분명 : 나프티핀염산염|분량 : 10|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '이 약 1그램 중', '수집URL': 'https://drug.hospitalk.net/item/201605527', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201605527', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200500806', 'ITEM_NAME': '나프노펜정(나프록센나트륨)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '나프록센나트륨', 'ENTP_NAME': '(주)일화', 'CHART': '연한 파란색의 타원형 필름코팅정', 'CHANGE_DATE': '2024-12-12', 'BAR_CODE': '8806409001400,8806409001417', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M070724]나프록센나트륨', '함량_원료성분원문': '총량 : 1정443.0밀리그램|성분명 : 나프록센나트륨|분량 : 275|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1443.0', '수집URL': 'https://drug.hospitalk.net/item/200500806', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200500806', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201701248', 'ITEM_NAME': '나프록소정(나프록센나트륨)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '나프록센나트륨', 'ENTP_NAME': '오스템파마주식회사', 'CHART': '흰색의 장방형 필름코팅정제', 'CHANGE_DATE': '2024-12-12', 'BAR_CODE': '8800535000207,8800535000214,8800535000221', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M070724]나프록센나트륨', '함량_원료성분원문': '총량 : 1정(430mg) 중|성분명 : 나프록센나트륨|분량 : 275.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정(430mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201701248', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201701248', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200204388', 'ITEM_NAME': '나프록신정(나프록센나트륨)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '나프록센나트륨', 'ENTP_NAME': '화일약품(주)', 'CHART': '청색의 타원형 필름코팅정제', 'CHANGE_DATE': '2024-12-12', 'BAR_CODE': '8800527006408,8800527006415,8806673000208,8806673000215,8806845014804,8806845014811,8806891001407,8806891001414', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M070724]나프록센나트륨', '함량_원료성분원문': '총량 : 1정(450.0mg)중|성분명 : 나프록센나트륨|분량 : 275.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정(450.0mg)중', '수집URL': 'https://drug.hospitalk.net/item/200204388', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200204388', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201902876', 'ITEM_NAME': '나프원큐연질캡슐(나프록센)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '나프록센', 'ENTP_NAME': '동아제약(주)', 'CHART': '무색 내지 연한 주황색의 투명한 내용물을 함유한 주황색의 투명한 타원형 연질캡슐', 'CHANGE_DATE': '2025-07-29', 'BAR_CODE': '8806265013005,8806265013012', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050116]나프록센', '함량_원료성분원문': '총량 : 1캡슐960밀리그램|성분명 : 나프록센|분량 : 250.000|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1960', '수집URL': 'https://drug.hospitalk.net/item/201902876', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201902876', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201607113', 'ITEM_NAME': '나프젠액1%(나프티핀염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '나프티핀염산염', 'ENTP_NAME': '현대약품(주)', 'CHART': '에탄올 냄새가 나는 무색 또는 미황색의 투명한 액체', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806420040204,8806420040211', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M253457]나프티핀염산염', '함량_원료성분원문': '총량 : 이 약 100 밀리리터 중|성분명 : 나프티핀염산염|분량 : 1.0|단위 : 그램|규격 : USP|성분정보 :', '함량_총량기준': '이 약 100 밀리리터 중', '수집URL': 'https://drug.hospitalk.net/item/201607113', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201607113', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201606467', 'ITEM_NAME': '나프젠크림(나프티핀염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '나프티핀염산염', 'ENTP_NAME': '현대약품(주)', 'CHART': '흰색의 크림제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806420040105,8806420040112', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M253457]나프티핀염산염', '함량_원료성분원문': '총량 : 1그램|성분명 : 나프티핀염산염|분량 : 10|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1그램', '수집URL': 'https://drug.hospitalk.net/item/201606467', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201606467', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201206888', 'ITEM_NAME': '나프졸액1%(나프티핀염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '나프티핀염산염', 'ENTP_NAME': '태극제약(주)', 'CHART': '에탄올 냄새가 나는 무색 또는 미황색의 투명한 액체', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806448045700,8806448045717', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M253457]나프티핀염산염', '함량_원료성분원문': '총량 : 이 약 100밀리리터 중|성분명 : 나프티핀염산염|분량 : 1.0|단위 : 그램|규격 : USP|성분정보 :', '함량_총량기준': '이 약 100밀리리터 중', '수집URL': 'https://drug.hospitalk.net/item/201206888', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201206888', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200803287', 'ITEM_NAME': '나프졸크림(나프티핀염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '나프티핀염산염', 'ENTP_NAME': '태극제약(주)', 'CHART': '백색의 크림제', 'CHANGE_DATE': '2013-09-13', 'BAR_CODE': '8806448033400,8806448033417', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M253457]나프티핀염산염', '함량_원료성분원문': '총량 : 이 약 1그램 중|성분명 : 나프티핀염산염|분량 : 10|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '이 약 1그램 중', '수집URL': 'https://drug.hospitalk.net/item/200803287', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200803287', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '197500016', 'ITEM_NAME': '낙센정(나프록센)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '나프록센', 'ENTP_NAME': '(주)종근당', 'CHART': '미황색(연노랑의) 장방형 정제', 'CHANGE_DATE': '2024-12-12', 'BAR_CODE': '8806433001209,8806433001216', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050116]나프록센', '함량_원료성분원문': '총량 : 이 약 1정(267 mg) 중|성분명 : 나프록센|분량 : 250|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 1정(267 mg) 중', '수집URL': 'https://drug.hospitalk.net/item/197500016', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=197500016', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202202115', 'ITEM_NAME': '내간애플러스연질캡슐(밀크시슬열매건조엑스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '밀크시슬열매건조엑스', 'ENTP_NAME': '초당약품공업(주)', 'CHART': '황갈색의 유상내용물을 함유한 암적색의 장방형연질캡슐', 'CHANGE_DATE': '2024-11-15', 'BAR_CODE': '8806707020400,8806707020417,8806707020424,8806707020431,8806707020448', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M268656]밀크시슬열매건조엑스', '함량_원료성분원문': '총량 : 1캡슐1,240밀리그램|성분명 : 밀크시슬열매건조엑스|분량 : 350.00|단위 : 밀리그램|규격 : 생규|성분정보 : 실리마린(으)로서 196 밀리그램', '함량_총량기준': '11,240', '수집URL': 'https://drug.hospitalk.net/item/202202115', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202202115', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202102183', 'ITEM_NAME': '내바렌큐액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': 'l-멘톨;리도카인;크로타미톤;클로트리마졸', 'ENTP_NAME': '부광약품(주)', 'CHART': '무색의 방향이 있는 맑은 액', 'CHANGE_DATE': '2024-02-23', 'BAR_CODE': '8806422045306,8806422045313', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M230875]l-멘톨|[M040131]리도카인|[M051499]크로타미톤|[M088335]클로트리마졸', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 클로트리마졸|분량 : 1.00|단위 : 그램|규격 : KP|성분정보 : ;총량 : 100밀리리터|성분명 : 크로타미톤|분량 : 5.00|단위 : 그램|규격 : USP|성분정보 : ;총량 : 100밀리리터|성분명 : 리도카인|분량 : 2.00|단위 : 그램|규격 : USP|성분정보 : ;총량 : 100밀리리터|성분명 : l-멘톨|분량 : 1.00|단위 : 그램|규격 : USP|성분정보 :', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/202102183', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202102183', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201606068', 'ITEM_NAME': '내시콜액(시메티콘)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시메티콘', 'ENTP_NAME': '(주)퍼슨', 'CHART': '딸기향이 나는 유백색의 현탁제', 'CHANGE_DATE': '2022-03-31', 'BAR_CODE': '8806574012102,8806574012119,8806574012126,8806574012133,8806574012140', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223083]시메티콘', '함량_원료성분원문': '총량 : 100밀리리터|성분명 : 시메티콘|분량 : 2|단위 : 그램|규격 : USP|성분정보 :', '함량_총량기준': '100', '수집URL': 'https://drug.hospitalk.net/item/201606068', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201606068', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199402372', 'ITEM_NAME': '네가펜캡슐(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '이소메텝턴뮤케이트;디크로랄페나존;아세트아미노펜', 'ENTP_NAME': '한국코러스(주)', 'CHART': '백색의 가루가 충진된 상, 하부 백색의 경질캡슐제', 'CHANGE_DATE': '2018-04-10', 'BAR_CODE': '8806472000102,8806472000119', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M082046]이소메텝턴뮤케이트|[M098569]디크로랄페나존|[M040353]아세트아미노펜', '함량_원료성분원문': '총량 : 1캡슐(607밀리그램) 중  |성분명 : 아세트아미노펜|분량 : 325|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(607밀리그램) 중  |성분명 : 디크로랄페나존|분량 : 100|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1캡슐(607밀리그램) 중  |성분명 : 이소메텝턴뮤케이트|분량 : 65|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1캡슐(607밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/199402372', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199402372', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202600999', 'ITEM_NAME': '네라민정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아스코르브산;니코틴산아미드;판토텐산칼슘;피리독신염산염;시아노코발라민 1000배산;리보플라빈;티아민질산염;폴산;D-비오틴', 'ENTP_NAME': '초당약품공업(주)', 'CHART': '담황색의 원형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806707022909,8806707022916,8806707022923', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M258994]아스코르브산|[M040064]니코틴산아미드|[M244748]판토텐산칼슘|[M204304]피리독신염산염|[M117558]시아노코발라민 1000배산|[M040133]리보플라빈|[M223262]티아민질산염|[M223289]폴산|[M249983]D-비오틴', '함량_원료성분원문': '총량 : 210밀리그램1정|성분명 : D-비오틴|분량 : 0.3|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 210밀리그램1정|성분명 : 폴산|분량 : 1.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 210밀리그램1정|성분명 : 티아민질산염|분량 : 1.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 210밀리그램1정|성분명 : 리보플라빈|분량 : 1.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 210밀리그램1정|성분명 : 시아노코발라민 1000배산|분량 : 6.0|단위 : 밀리그램|규격 : KP|성분정보 : 시아노코발라민((으)로서 6.0 마이크로그램;총량 : 210밀리그램1정|성분명 : 피리독신염산염|분량 : 10.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 210밀리그램1정|성분명 : 판토텐산칼슘|분량 : 10.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 210밀리그램1정|성분명 : 니코틴산아미드|분량 : 20.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 210밀리그램1정|성분명 : 아스코르브산|분량 : 60.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '2101', '수집URL': 'https://drug.hospitalk.net/item/202600999', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202600999', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201201967', 'ITEM_NAME': '네로민정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '판토텐산칼슘;니코틴산아미드;d-비오틴;폴산;제피아스코르브산;리보플라빈;시아노코발라민 1000배산;티아민질산염;피리독신염산염', 'ENTP_NAME': '(주)한풍제약', 'CHART': '주황색의 원형 필름코팅정', 'CHANGE_DATE': '2022-08-26', 'BAR_CODE': '8806472053009,8806472053016,8806472053023,8806581081702,8806581081719,8806704016000,8806704016017,8806704016024,8806706061008,8806706061015,8806706061022,8806706076705,8806706076712,8806706076729', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M244748]판토텐산칼슘|[M040064]니코틴산아미드|[M249150]d-비오틴|[M223289]폴산|[M236913]제피아스코르브산|[M040133]리보플라빈|[M117558]시아노코발라민 1000배산|[M223262]티아민질산염|[M204304]피리독신염산염', '함량_원료성분원문': '총량 : 1정208.5밀리그램|성분명 : 피리독신염산염|분량 : 10.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정208.5밀리그램|성분명 : 티아민질산염|분량 : 1.50|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정208.5밀리그램|성분명 : 시아노코발라민 1000배산|분량 : 6.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정208.5밀리그램|성분명 : 리보플라빈|분량 : 1.70|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정208.5밀리그램|성분명 : 제피아스코르브산|분량 : 61.86|단위 : 밀리그램|규격 : 별규|성분정보 : 아스코르브산(으)로서 60 밀리그램;총량 : 1정208.5밀리그램|성분명 : 폴산|분량 : 1.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정208.5밀리그램|성분명 : d-비오틴|분량 : 0.30|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1정208.5밀리그램|성분명 : 니코틴산아미드|분량 : 20.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정208.5밀리그램|성분명 : 판토텐산칼슘|분량 : 10.00|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1208.5', '수집URL': 'https://drug.hospitalk.net/item/201201967', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201201967', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199600258', 'ITEM_NAME': '네오고비온캅셀(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '엽산;황산동;글루콘산제일철;시아노코발라민0ㆍ1%;황산망간;아스코르빈산97%', 'ENTP_NAME': '(주)유유제약', 'CHART': '회갈색 분말을 함유하는 상하 흑갈색 경질캅셀제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806445001006', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040442]엽산|[M040799]황산동|[M070072]글루콘산제일철|[M083188]시아노코발라민0ㆍ1%|[M051962]황산망간|[M084448]아스코르빈산97%', '함량_원료성분원문': '총량 : 1캡슐 중 457밀리그램|성분명 : 아스코르빈산97%|분량 : 51.5|단위 : 밀리그램|규격 : 별규|성분정보 : 아스코르빈산으로서 50밀리그램;총량 : 1캡슐 중 457밀리그램|성분명 : 황산망간|분량 : 200|단위 : 마이크로그램|규격 : USP|성분정보 : 망간으로서 65마이크로그램;총량 : 1캡슐 중 457밀리그램|성분명 : 시아노코발라민0ㆍ1%|분량 : 7.5|단위 : 밀리그램|규격 : 식약본부고시제1996-2호|성분정보 : 시아노코발라민으로서 7.5마이크로그램;총량 : 1캡슐 중 457밀리그램|성분명 : 글루콘산제일철|분량 : 250|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐 중 457밀리그램|성분명 : 황산동|분량 : 200|단위 : 마이크로그램|규격 : 식약본부고시제1996-2호|성분정보 : 동으로서 50.9마이크로그램;총량 : 1캡슐 중 457밀리그램|성분명 : 엽산|분량 : 1|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1캡슐 중 457밀리그램', '수집URL': 'https://drug.hospitalk.net/item/199600258', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199600258', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201109156', 'ITEM_NAME': '네오목신크림(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '폴리믹신B황산염;프라목신염산염;네오마이신황산염', 'ENTP_NAME': '주식회사제뉴원사이언스', 'CHART': '흰색의 크림제', 'CHANGE_DATE': '2015-01-20', 'BAR_CODE': '8806717035807,8806717035814', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M233313]폴리믹신B황산염|[M246661]프라목신염산염|[M202893]네오마이신황산염', '함량_원료성분원문': '총량 : 이 약 1g 중|성분명 : 폴리믹신B황산염|분량 : 10000|단위 : 아이.유|규격 : USP|성분정보 : ;총량 : 이 약 1g 중|성분명 : 프라목신염산염|분량 : 10|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 이 약 1g 중|성분명 : 네오마이신황산염|분량 : 3.5|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 1g 중', '수집URL': 'https://drug.hospitalk.net/item/201109156', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201109156', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201007716', 'ITEM_NAME': '네오시네프린나잘액1%(페닐레프린염산염)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '페닐레프린염산염', 'ENTP_NAME': '태극제약(주)', 'CHART': '무색내지 미황색의 투명한 액제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806448045007', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M222724]페닐레프린염산염', '함량_원료성분원문': '총량 : 이 약 1밀리리터 중|성분명 : 페닐레프린염산염|분량 : 10|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '이 약 1밀리리터 중', '수집URL': 'https://drug.hospitalk.net/item/201007716', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201007716', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199801121', 'ITEM_NAME': '네오시덤연고(퓨시드산나트륨)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '퓨시드산나트륨', 'ENTP_NAME': '태극제약(주)', 'CHART': '무색 또는 연한 노란색의 연고제', 'CHANGE_DATE': '2021-07-23', 'BAR_CODE': '8806448001904,8806448001911,8806448001928,8806448001935,8806448001942,8806448001959', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M243954]퓨시드산나트륨', '함량_원료성분원문': '총량 : 이 약 1그램 중|성분명 : 퓨시드산나트륨|분량 : 20|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 1그램 중', '수집URL': 'https://drug.hospitalk.net/item/199801121', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199801121', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202303220', 'ITEM_NAME': '네오신정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '판토텐산칼슘;니코틴산아미드;D-비오틴;폴산;아스코르브산;리보플라빈;시아노코발라민 1000배산;티아민질산염;피리독신염산염', 'ENTP_NAME': '메딕스제약(주)', 'CHART': '담황색의 원형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806258015306,8806258015313,8806258015320', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M244748]판토텐산칼슘|[M040064]니코틴산아미드|[M249983]D-비오틴|[M223289]폴산|[M258994]아스코르브산|[M040133]리보플라빈|[M117558]시아노코발라민 1000배산|[M223262]티아민질산염|[M204304]피리독신염산염', '함량_원료성분원문': '총량 : 1정210밀리그램|성분명 : 피리독신염산염|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정210밀리그램|성분명 : 티아민질산염|분량 : 1.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정210밀리그램|성분명 : 시아노코발라민 1000배산|분량 : 6|단위 : 밀리그램|규격 : KP|성분정보 : 시아노코발라민(으)로서 6 마이크로그램;총량 : 1정210밀리그램|성분명 : 리보플라빈|분량 : 1.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정210밀리그램|성분명 : 아스코르브산|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정210밀리그램|성분명 : 폴산|분량 : 1|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정210밀리그램|성분명 : D-비오틴|분량 : 0.3|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1정210밀리그램|성분명 : 니코틴산아미드|분량 : 20|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정210밀리그램|성분명 : 판토텐산칼슘|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1210', '수집URL': 'https://drug.hospitalk.net/item/202303220', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202303220', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200810815', 'ITEM_NAME': '네오실리칸연질캡슐(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시아노코발라민;판토텐산칼슘;니코틴산아미드;피리독신염산염;리보플라빈;티아민염산염;밀크시슬엑스', 'ENTP_NAME': '(주)유영제약', 'CHART': '황갈색의 점조성 내용물이 든 암록색의 장방형 연질캡슐제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806482034203', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M096429]시아노코발라민|[M244748]판토텐산칼슘|[M040064]니코틴산아미드|[M204304]피리독신염산염|[M040133]리보플라빈|[M223258]티아민염산염|[M250889]밀크시슬엑스', '함량_원료성분원문': '총량 : 1캡슐(1,231mg)중|성분명 : 밀크시슬엑스|분량 : 200.0|단위 : 밀리그램|규격 : DAB|성분정보 : ;총량 : 1캡슐(1,231mg)중|성분명 : 티아민염산염|분량 : 8.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,231mg)중|성분명 : 리보플라빈|분량 : 8.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,231mg)중|성분명 : 피리독신염산염|분량 : 8.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,231mg)중|성분명 : 니코틴산아미드|분량 : 24.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,231mg)중|성분명 : 판토텐산칼슘|분량 : 16.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐(1,231mg)중|성분명 : 시아노코발라민|분량 : 2.4|단위 : 마이크로그램|규격 : KP|성분정보 :', '함량_총량기준': '1캡슐(1,231mg)중', '수집URL': 'https://drug.hospitalk.net/item/200810815', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200810815', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200801383', 'ITEM_NAME': '네오칼디정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '농축콜레칼시페롤;구연산칼슘', 'ENTP_NAME': '주식회사제뉴원사이언스', 'CHART': '흰색의 장방형 정제', 'CHANGE_DATE': '2012-07-03', 'BAR_CODE': '8806717020902,8806717020919,8806717020926,8806717020933', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M086116]농축콜레칼시페롤|[M050064]구연산칼슘', '함량_원료성분원문': '총량 : 1정(1,050mg)중|성분명 : 구연산칼슘|분량 : 750|단위 : 밀리그램|규격 : USP|성분정보 : 칼슘으로서 158mg;총량 : 1정(1,050mg)중|성분명 : 농축콜레칼시페롤|분량 : 4|단위 : 밀리그램|규격 : EP|성분정보 : 비타민D로서 400IU', '함량_총량기준': '1정(1,050mg)중-(내수용, 수출용)', '수집URL': 'https://drug.hospitalk.net/item/200801383', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200801383', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202503409', 'ITEM_NAME': '네오칼시돌연질캡슐0.5마이크로그램(알파칼시돌)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '알파칼시돌', 'ENTP_NAME': '(주)녹십자', 'CHART': '무색 또는 투명한 유상 내용물이 들어있는 노란색의 타원형 연질캡슐', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806436070202,8806436070219,8806436070226', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081303]알파칼시돌', '함량_원료성분원문': '총량 : 1캡슐270.081밀리그램|성분명 : 알파칼시돌|분량 : 0.50|단위 : 마이크로그램|규격 : EP|성분정보 :', '함량_총량기준': '1270.081', '수집URL': 'https://drug.hospitalk.net/item/202503409', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202503409', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202503410', 'ITEM_NAME': '네오칼시돌연질캡슐1마이크로그램(알파칼시돌)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '알파칼시돌', 'ENTP_NAME': '(주)녹십자', 'CHART': '무색 또는 투명한 유상 내용물이 들어있는 주황색의 타원형 연질캡슐', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806436070301,8806436070318,8806436070325', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M081303]알파칼시돌', '함량_원료성분원문': '총량 : 1캡슐270.081밀리그램|성분명 : 알파칼시돌|분량 : 1.00|단위 : 마이크로그램|규격 : EP|성분정보 :', '함량_총량기준': '1270.081', '수집URL': 'https://drug.hospitalk.net/item/202503410', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202503410', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202500672', 'ITEM_NAME': '네오칼큐정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '티아민염산염;폴산;콜레칼시페롤농축분말;시트르산칼슘수화물', 'ENTP_NAME': '주식회사제뉴원사이언스', 'CHART': '분홍색의 장방형 필름코팅정', 'CHANGE_DATE': '2025-03-27', 'BAR_CODE': '8806717074806,8806717074813,8806717074820', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223258]티아민염산염|[M223289]폴산|[M102050]콜레칼시페롤농축분말|[M247470]시트르산칼슘수화물', '함량_원료성분원문': '총량 : 1정644밀리그램|성분명 : 시트르산칼슘수화물|분량 : 475|단위 : 밀리그램|규격 : USP|성분정보 : 칼슘(으)로서 100.11 밀리그램;총량 : 1정644밀리그램|성분명 : 콜레칼시페롤농축분말|분량 : 10|단위 : 밀리그램|규격 : EP|성분정보 : 비타민D(으)로서 1,000 아이.유;총량 : 1정644밀리그램|성분명 : 폴산|분량 : 1|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정644밀리그램|성분명 : 티아민염산염|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1644', '수집URL': 'https://drug.hospitalk.net/item/202500672', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202500672', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201706691', 'ITEM_NAME': '네오콜캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '카페인무수물;클로르페니라민말레산염;티페피딘히벤즈산염;아세트아미노펜;소청룡탕건조엑스', 'ENTP_NAME': '한국신텍스제약(주)', 'CHART': '암갈색의 분말이 든 상부 적갈색 하부 미황색의 경질 캡슐', 'CHANGE_DATE': '2025-11-10', 'BAR_CODE': '8806230049206,8806230049213', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223183]카페인무수물|[M223211]클로르페니라민말레산염|[M223273]티페피딘히벤즈산염|[M040353]아세트아미노펜|[M040140]소청룡탕건조엑스', '함량_원료성분원문': '총량 : 1캡슐540밀리그램|성분명 : 소청룡탕건조엑스|분량 : 200.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1캡슐540밀리그램|성분명 : 아세트아미노펜|분량 : 150.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐540밀리그램|성분명 : 티페피딘히벤즈산염|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐540밀리그램|성분명 : 클로르페니라민말레산염|분량 : 1.25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐540밀리그램|성분명 : 카페인무수물|분량 : 12.5|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1540', '수집URL': 'https://drug.hospitalk.net/item/201706691', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201706691', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201800286', 'ITEM_NAME': '네오콜코프캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '길경가루;감초가루;카르비녹사민말레산염;구아야콜설폰산칼륨;노스카핀;dl-메틸에페드린염산염;덱스트로메토르판브롬화수소산염수화물', 'ENTP_NAME': '한국신텍스제약(주)', 'CHART': '미황색의 분말이 든 상부 담청색 하부 백색의 경질캡슐', 'CHANGE_DATE': '2022-11-02', 'BAR_CODE': '8806230049800,8806230049817', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M082634]길경가루|[M070009]감초가루|[M251260]카르비녹사민말레산염|[M050059]구아야콜설폰산칼륨|[M040059]노스카핀|[M204422]dl-메틸에페드린염산염|[M222957]덱스트로메토르판브롬화수소산염수화물', '함량_원료성분원문': '총량 : 1캡슐(580mg)중|성분명 : 덱스트로메토르판브롬화수소산염수화물|분량 : 10.0|단위 : 밀리그램|규격 : KP|성분정보 : 활성물질용량;총량 : 1캡슐(580mg)중|성분명 : dl-메틸에페드린염산염|분량 : 12.5|단위 : 밀리그램|규격 : KP|성분정보 : 활성물질용량;총량 : 1캡슐(580mg)중|성분명 : 노스카핀|분량 : 10.0|단위 : 밀리그램|규격 : KP|성분정보 : 활성물질용량;총량 : 1캡슐(580mg)중|성분명 : 구아야콜설폰산칼륨|분량 : 45.0|단위 : 밀리그램|규격 : KP|성분정보 : 활성물질용량;총량 : 1캡슐(580mg)중|성분명 : 카르비녹사민말레산염|분량 : 2.0|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1캡슐(580mg)중|성분명 : 감초가루|분량 : 100.0|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1캡슐(580mg)중|성분명 : 길경가루|분량 : 150.0|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1캡슐(580mg)중', '수집URL': 'https://drug.hospitalk.net/item/201800286', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201800286', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200204181', 'ITEM_NAME': '네오퀸크림4%(히드로퀴논)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '히드로퀴논', 'ENTP_NAME': '(주)나노팜', 'CHART': '백색의 크림', 'CHANGE_DATE': '2022-03-31', 'BAR_CODE': '8806589000507,8806589000514,8806589000521,8806589000538', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051981]히드로퀴논', '함량_원료성분원문': '총량 : 1g 중|성분명 : 히드로퀴논|분량 : 40|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1g 중', '수집URL': 'https://drug.hospitalk.net/item/200204181', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200204181', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200905161', 'ITEM_NAME': '네오큐란연질캡슐(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '마늘유;은행엽엑스;멜리사엽엑스;서양산사60%에탄올엑스', 'ENTP_NAME': '(주)마더스제약', 'CHART': '암갈색의 유상물질이 들어있는 연초록의 타원형 연질캅셀', 'CHANGE_DATE': '2014-09-29', 'BAR_CODE': '8806228005306,8806552021300', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M086537]마늘유|[M080879]은행엽엑스|[M095632]멜리사엽엑스|[M092882]서양산사60%에탄올엑스', '함량_원료성분원문': '총량 : 1캡슐(649.1mg)중|성분명 : 서양산사60%에탄올엑스|분량 : 50|단위 : 밀리그램|규격 : KPC|성분정보 : ;총량 : 1캡슐(649.1mg)중|성분명 : 멜리사엽엑스|분량 : 10|단위 : 밀리그램|규격 : KPC|성분정보 : ;총량 : 1캡슐(649.1mg)중|성분명 : 은행엽엑스|분량 : 5|단위 : 밀리그램|규격 : KPC|성분정보 : ;총량 : 1캡슐(649.1mg)중|성분명 : 마늘유|분량 : 150|단위 : 밀리그램|규격 : KPC|성분정보 :', '함량_총량기준': '1캡슐(649.1mg)중', '수집URL': 'https://drug.hospitalk.net/item/200905161', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200905161', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201803647', 'ITEM_NAME': '네오크로신연질캡슐(클로닉신리시네이트)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로닉신리시네이트', 'ENTP_NAME': '(주)넥스팜코리아', 'CHART': '미황색의 투명한 액이 든 청색의 투명한 타원형 연질캡슐', 'CHANGE_DATE': '2019-11-11', 'BAR_CODE': '8806625040504,8806625040511', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M080375]클로닉신리시네이트', '함량_원료성분원문': '총량 : 이 약 1캡슐 (860mg) 중|성분명 : 클로닉신리시네이트|분량 : 125.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '이 약 1캡슐 (860mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201803647', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201803647', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200801735', 'ITEM_NAME': '네오탄연고', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '네오마이신황산염;히드로코르티손아세테이트;센텔라정량추출물', 'ENTP_NAME': '정우신약(주)', 'CHART': '백색 내지 미황색의 전질균등한 연고제', 'CHANGE_DATE': '2018-07-18', 'BAR_CODE': '8806452035506,8806452035513,8806625020001,8806625020018,8806638028100,8806638028117,8806942043202,8806942043219', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M202893]네오마이신황산염|[M223353]히드로코르티손아세테이트|[M251396]센텔라정량추출물', '함량_원료성분원문': '총량 : 1g 중|성분명 : 센텔라정량추출물|분량 : 10.0|단위 : 밀리그램|규격 : 생규|성분정보 : 아시아티코사이드로서 4mg;총량 : 1g 중|성분명 : 히드로코르티손아세테이트|분량 : 10.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1g 중|성분명 : 네오마이신황산염|분량 : 3.5|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1g 중', '수집URL': 'https://drug.hospitalk.net/item/200801735', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200801735', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202501961', 'ITEM_NAME': '네오펙소정120밀리그램(펙소페나딘염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '펙소페나딘염산염', 'ENTP_NAME': '(주)녹십자', 'CHART': '연분홍색의 타원형 필름코팅정', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806436069107,8806436069114,8806436069121,8806436069138,8806436069145', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M246634]펙소페나딘염산염', '함량_원료성분원문': '총량 : 1정229밀리그램|성분명 : 펙소페나딘염산염|분량 : 120.00|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1229', '수집URL': 'https://drug.hospitalk.net/item/202501961', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202501961', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200701026', 'ITEM_NAME': '네오폴신연고(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '네오마이신황산염;폴리믹신B황산염;바시트라신', 'ENTP_NAME': '(주)에이프로젠바이오로직스', 'CHART': '백색의 연고제', 'CHANGE_DATE': '2020-09-25', 'BAR_CODE': '8806452053005,8806518001407', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M202893]네오마이신황산염|[M233313]폴리믹신B황산염|[M020054]바시트라신', '함량_원료성분원문': '총량 : 1그람 중|성분명 : 네오마이신황산염|분량 : 3.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그람 중|성분명 : 폴리믹신B황산염|분량 : 5000|단위 : 유니트|규격 : KP|성분정보 : ;총량 : 1그람 중|성분명 : 바시트라신|분량 : 400|단위 : 유니트|규격 : KP|성분정보 :', '함량_총량기준': '1그람 중', '수집URL': 'https://drug.hospitalk.net/item/200701026', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200701026', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201705764', 'ITEM_NAME': '네오프라신연고', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '네오마이신황산염;폴리믹신B황산염;바시트라신아연;프라목신염산염', 'ENTP_NAME': '(주)테라젠이텍스', 'CHART': '흰색 또는 미황색의 연고제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806985037404,8806985037411', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M202893]네오마이신황산염|[M233313]폴리믹신B황산염|[M083538]바시트라신아연|[M246661]프라목신염산염', '함량_원료성분원문': '총량 : 1g 중|성분명 : 네오마이신황산염|분량 : 3.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1g 중|성분명 : 폴리믹신B황산염|분량 : 10000.0|단위 : 유니트|규격 : USP|성분정보 : ;총량 : 1g 중|성분명 : 바시트라신아연|분량 : 500.0|단위 : 유니트|규격 : USP|성분정보 : ;총량 : 1g 중|성분명 : 프라목신염산염|분량 : 10.0|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1g 중', '수집URL': 'https://drug.hospitalk.net/item/201705764', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201705764', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201505910', 'ITEM_NAME': '네일스타네일라카(시클로피록스)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '시클로피록스', 'ENTP_NAME': '부광약품(주)', 'CHART': '브러쉬가 부착된 뚜껑이 있는 유리병안에든 무색~엷은 황색의 투명한 액제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806422039602,8806422039619,8806422039626', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M085228]시클로피록스', '함량_원료성분원문': '총량 : 이 약 1g 중|성분명 : 시클로피록스|분량 : 80|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '이 약 1g 중', '수집URL': 'https://drug.hospitalk.net/item/201505910', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201505910', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200402464', 'ITEM_NAME': '네프리스에스정(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '레스트애로우근30%에탄올건조엑스(6.5→1);오르소시폰엽40%에탄올건조엑스(5→1);골든로드50%에탄올건조엑스(5.5→1)', 'ENTP_NAME': '(주)팜젠사이언스', 'CHART': '녹색 장방형의 필름코팅정제', 'CHANGE_DATE': '2013-09-11', 'BAR_CODE': '8806701000408,8806701000415,8806701000422,8806701000439,8806701000446', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M284618]레스트애로우근30%에탄올건조엑스(6.5→1)|[M284617]오르소시폰엽40%에탄올건조엑스(5→1)|[M284619]골든로드50%에탄올건조엑스(5.5→1)', '함량_원료성분원문': '총량 : 1정 (630mg) 중|성분명 : 레스트애로우근30%에탄올건조엑스(6.5→1)|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1정 (630mg) 중|성분명 : 오르소시폰엽40%에탄올건조엑스(5→1)|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : 시넨세틴으로서 0.1mg;총량 : 1정 (630mg) 중|성분명 : 골든로드50%에탄올건조엑스(5.5→1)|분량 : 200|단위 : 밀리그램|규격 : 생규|성분정보 : 총 플라보노이드로서 10.0mg', '함량_총량기준': '1정 (630mg) 중', '수집URL': 'https://drug.hospitalk.net/item/200402464', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200402464', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201600782', 'ITEM_NAME': '네프리스엔정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '레스트애로우근엑스(5∼8→1)·유당수화물혼합물(4:1);오르소시폰엽엑스(5∼7→1)·스프레이건조글루코스액혼합물(9:1);골든로드엑스(4∼7→1)·말토덱스트린혼합물(9:1)', 'ENTP_NAME': '(주)팜젠사이언스', 'CHART': '녹색 장방형의 필름코팅정제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806701039309,8806701039316,8806701039323,8806701039330,8806701039347,8806701039354', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M263532]레스트애로우근엑스(5∼8→1)·유당수화물혼합물(4:1)|[M263533]오르소시폰엽엑스(5∼7→1)·스프레이건조글루코스액혼합물(9:1)|[M263534]골든로드엑스(4∼7→1)·말토덱스트린혼합물(9:1)', '함량_원료성분원문': '총량 : 1정 (580mg) 중|성분명 : 레스트애로우근엑스(5∼8→1)·유당수화물혼합물(4:1)|분량 : 80|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1정 (580mg) 중|성분명 : 오르소시폰엽엑스(5∼7→1)·스프레이건조글루코스액혼합물(9:1)|분량 : 90|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1정 (580mg) 중|성분명 : 골든로드엑스(4∼7→1)·말토덱스트린혼합물(9:1)|분량 : 180|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1정 (580mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201600782', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201600782', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200402462', 'ITEM_NAME': '네프리스연질캡슐(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '레스트애로우근30%에탄올건조엑스(6.5→1);오르소시폰엽40%에탄올건조엑스(5→1);베어베리엽건조엑스', 'ENTP_NAME': '(주)팜젠사이언스', 'CHART': '담황갈색의 반고형성 내용물이 들어있는 한면 암녹색, 한면 녹색의 장방형 연질캡슐제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806701000507,8806701000514', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M284618]레스트애로우근30%에탄올건조엑스(6.5→1)|[M284617]오르소시폰엽40%에탄올건조엑스(5→1)|[M284616]베어베리엽건조엑스', '함량_원료성분원문': '총량 : 1캡슐(891.0mg) 중|성분명 : 베어베리엽건조엑스|분량 : 80|단위 : 밀리그램|규격 : 생규|성분정보 : 알부틴으로서8mg;총량 : 1캡슐(891.0mg) 중|성분명 : 오르소시폰엽40%에탄올건조엑스(5→1)|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : 시넨세틴으로서0.1mg;총량 : 1캡슐(891.0mg) 중|성분명 : 레스트애로우근30%에탄올건조엑스(6.5→1)|분량 : 30|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1캡슐(891.0mg) 중', '수집URL': 'https://drug.hospitalk.net/item/200402462', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200402462', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199802000', 'ITEM_NAME': '네프비타정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '피리독신염산염;티아민질산염;시아노코발라민 1000배산;아스코르브산;폴산;비오틴;니코틴산아미드;판토텐산칼슘;리보플라빈', 'ENTP_NAME': '하이플생명과학(주)', 'CHART': '주황색의 원형 필름코팅정', 'CHANGE_DATE': '2026-07-20', 'BAR_CODE': '8806641000308,8806641000315,8806641000322,8806641000339', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M204304]피리독신염산염|[M223262]티아민질산염|[M117558]시아노코발라민 1000배산|[M258994]아스코르브산|[M223289]폴산|[M050704]비오틴|[M040064]니코틴산아미드|[M244748]판토텐산칼슘|[M040133]리보플라빈', '함량_원료성분원문': '총량 : 1정418밀리그램|성분명 : 피리독신염산염|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정418밀리그램|성분명 : 티아민질산염|분량 : 1.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정418밀리그램|성분명 : 시아노코발라민 1000배산|분량 : 6|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정418밀리그램|성분명 : 아스코르브산|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정418밀리그램|성분명 : 폴산|분량 : 800|단위 : 마이크로그램|규격 : KP|성분정보 : ;총량 : 1정418밀리그램|성분명 : 비오틴|분량 : 300|단위 : 마이크로그램|규격 : USP|성분정보 : ;총량 : 1정418밀리그램|성분명 : 니코틴산아미드|분량 : 20|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정418밀리그램|성분명 : 판토텐산칼슘|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정418밀리그램|성분명 : 리보플라빈|분량 : 1.7|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1418', '수집URL': 'https://drug.hospitalk.net/item/199802000', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199802000', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201405845', 'ITEM_NAME': '네프신정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '황금;택사;차전자;감초;치자;목통;당귀;연교;마황;대황;생강;육계;지황;용담', 'ENTP_NAME': '한솔신약(주)', 'CHART': '황갈색의 원형 정제', 'CHANGE_DATE': '2017-09-05', 'BAR_CODE': '8806458040603,8806458040610,8806458040627,8806458040634', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040789]황금|[M040638]택사|[M040545]차전자|[M040006]감초|[M040564]치자|[M040186]목통|[M040070]당귀|[M051105]연교|[M040135]마황|[M040073]대황|[M050752]생강|[M050036]육계|[M040537]지황|[M040474]용담', '함량_원료성분원문': '총량 : 1정(300mg) 중|성분명 : 지황|분량 : 416.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(300mg) 중|성분명 : 육계|분량 : 16.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(300mg) 중|성분명 : 생강|분량 : 16.7|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1정(300mg) 중|성분명 : 대황|분량 : 16.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(300mg) 중|성분명 : 마황|분량 : 16.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(300mg) 중|성분명 : 연교|분량 : 16.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(300mg) 중|성분명 : 당귀|분량 : 416.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(300mg) 중|성분명 : 목통|분량 : 416.7|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(300mg) 중|성분명 : 황금|분량 : 250.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(300mg) 중|성분명 : 택사|분량 : 250.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(300mg) 중|성분명 : 차전자|분량 : 250.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(300mg) 중|성분명 : 감초|분량 : 125.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(300mg) 중|성분명 : 치자|분량 : 125.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정(300mg) 중|성분명 : 용담|분량 : 125.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정(300mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201405845', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201405845', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200810270', 'ITEM_NAME': '넥스콜환(은교산환)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '은교산건조엑스', 'ENTP_NAME': '한솔신약(주)', 'CHART': '흑갈색의 환제', 'CHANGE_DATE': '2010-06-20', 'BAR_CODE': '8806458014505,8806458014512,8806458014529', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M095416]은교산건조엑스', '함량_원료성분원문': '총량 : 1포 (20환) 중|성분명 : 은교산건조엑스|분량 : 500|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1포 (20환) 중', '수집URL': 'https://drug.hospitalk.net/item/200810270', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200810270', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201309307', 'ITEM_NAME': '넥스팜실리마린정(밀크시슬엑스)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '밀크시슬엑스', 'ENTP_NAME': '(주)넥스팜코리아', 'CHART': '갈색의 원형 필름코팅정제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806625028908', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M250889]밀크시슬엑스', '함량_원료성분원문': '총량 : 이 약 1정(547.0mg) 중|성분명 : 밀크시슬엑스|분량 : 200.0|단위 : 밀리그램|규격 : 생규|성분정보 : 실리빈으로서 60mg', '함량_총량기준': '이 약 1정(547.0mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201309307', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201309307', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199804331', 'ITEM_NAME': '넥스팜염산암부록솔정(암브록솔염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '암브록솔염산염', 'ENTP_NAME': '(주)넥스팜코리아', 'CHART': '흰색의 원형정제', 'CHANGE_DATE': '2023-06-07', 'BAR_CODE': '8806625003103,8806625003110,8806625003127', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M233843]암브록솔염산염', '함량_원료성분원문': '총량 : 1정 (180mg) 중|성분명 : 암브록솔염산염|분량 : 30|단위 : 밀리그램|규격 : EP|성분정보 :', '함량_총량기준': '1정 (180mg) 중', '수집URL': 'https://drug.hospitalk.net/item/199804331', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199804331', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198601617', 'ITEM_NAME': '넥스팜염화리소짐90밀리그람정(수출명:ENTASE Tab.)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '리소짐염산염', 'ENTP_NAME': '(주)넥스팜코리아', 'CHART': '분홍색의 원형 필름코팅정제', 'CHANGE_DATE': '2013-09-06', 'BAR_CODE': '8806625003400,8806625003417,8806625003424,8806625003431', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256212]리소짐염산염', '함량_원료성분원문': '총량 : 1정 (250.3mg) 중|성분명 : 리소짐염산염|분량 : 90|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정 (250.3mg) 중', '수집URL': 'https://drug.hospitalk.net/item/198601617', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198601617', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199804362', 'ITEM_NAME': '넥스팜탄산칼슘정(침강탄산칼슘)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '침강탄산칼슘', 'ENTP_NAME': '(주)넥스팜코리아', 'CHART': '흰색의 원형 정제', 'CHANGE_DATE': '2020-08-18', 'BAR_CODE': '8806625003608,8806625003615,8806625003622,8806625003639', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040634]침강탄산칼슘', '함량_원료성분원문': '총량 : 1정 (650.0mg) 중|성분명 : 침강탄산칼슘|분량 : 500.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정 (650.0mg) 중', '수집URL': 'https://drug.hospitalk.net/item/199804362', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199804362', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201310349', 'ITEM_NAME': '넥스핀장용정100mg(아스피린)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아스피린', 'ENTP_NAME': '(주)넥스팜코리아', 'CHART': '흰색의 원형 장용성 필름코팅정', 'CHANGE_DATE': '2025-04-15', 'BAR_CODE': '8806625028502,8806625028519,8806625028526', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040355]아스피린', '함량_원료성분원문': '총량 : 1정 (157.0mg) 중|성분명 : 아스피린|분량 : 100.0|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1정 (157.0mg) 중', '수집URL': 'https://drug.hospitalk.net/item/201310349', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201310349', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202200157', 'ITEM_NAME': '넥시겔현탁액(수출명: Nexigel suspension)(수출용)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '수산화마그네슘;건조수산화알루미늄 겔;옥세타자인', 'ENTP_NAME': '(주)넥스팜코리아', 'CHART': '알루미늄 호일 파우치에 들어있는 향기가 있는 흰색의 현탁액', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806625043307,8806625043314,8806625043321', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040306]수산화마그네슘|[M229291]건조수산화알루미늄 겔|[M201415]옥세타자인', '함량_원료성분원문': '총량 : 1포10밀리리터|성분명 : 옥세타자인|분량 : 20|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포10밀리리터|성분명 : 건조수산화알루미늄 겔|분량 : 582|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포10밀리리터|성분명 : 수산화마그네슘|분량 : 196|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '110', '수집URL': 'https://drug.hospitalk.net/item/202200157', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202200157', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201804383', 'ITEM_NAME': '넥콘600에프정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '리보플라빈;시아노코발라민1000배산;피리독신염산염;판토텐산 칼슘;콜린타르타르산염;이노시톨;니코틴산아미드;푸르설티아민;콜레칼시페롤과립;γ-오리자놀;콘드로이틴설페이트나트륨', 'ENTP_NAME': '(주)넥스팜코리아', 'CHART': '갈색의 장방형 필름코팅정제', 'CHANGE_DATE': '2023-12-06', 'BAR_CODE': '8806625040801,8806625040818', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040133]리보플라빈|[M255994]시아노코발라민1000배산|[M204304]피리독신염산염|[M225044]판토텐산 칼슘|[M247683]콜린타르타르산염|[M040488]이노시톨|[M040064]니코틴산아미드|[M051415]푸르설티아민|[M099907]콜레칼시페롤과립|[M208932]γ-오리자놀|[M256191]콘드로이틴설페이트나트륨', '함량_원료성분원문': '총량 : 1정 (1134.0밀리그램) 중|성분명 : 콘드로이틴설페이트나트륨|분량 : 600.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 (1134.0밀리그램) 중|성분명 : γ-오리자놀|분량 : 5.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 (1134.0밀리그램) 중|성분명 : 콜레칼시페롤과립|분량 : 0.5|단위 : 밀리그램|규격 : EP|성분정보 : 콜레칼시페롤로서50IU;총량 : 1정 (1134.0밀리그램) 중|성분명 : 푸르설티아민|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 (1134.0밀리그램) 중|성분명 : 니코틴산아미드|분량 : 50.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 (1134.0밀리그램) 중|성분명 : 이노시톨|분량 : 25.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 (1134.0밀리그램) 중|성분명 : 콜린타르타르산염|분량 : 20.0|단위 : 밀리그램|규격 : 별규|성분정보 : ;총량 : 1정 (1134.0밀리그램) 중|성분명 : 판토텐산 칼슘|분량 : 15.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 (1134.0밀리그램) 중|성분명 : 피리독신염산염|분량 : 10.0|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1정 (1134.0밀리그램) 중|성분명 : 시아노코발라민1000배산|분량 : 10.0|단위 : 밀리그램|규격 : KP|성분정보 : 시아노코발라민으로서10ug;총량 : 1정 (1134.0밀리그램) 중|성분명 : 리보플라빈|분량 : 6.0|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정 (1134.0밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201804383', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201804383', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200902637', 'ITEM_NAME': '넥크린과립(향성파적환)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '가자;아선약;대황;박하;천궁;사인;감초;길경;이상수침건조엑스;연교', 'ENTP_NAME': '한솔신약(주)', 'CHART': '흑갈색의 과립제', 'CHANGE_DATE': '2019-01-15', 'BAR_CODE': '8806458042003,8806458042010,8806458042027,8806585009702,8806585009719,8806585009726,8806585009733,8806585009740', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M050005]가자|[M040350]아선약|[M040073]대황|[M040198]박하|[M040550]천궁|[M095260]사인|[M040006]감초|[M040048]길경|[M099148]이상수침건조엑스|[M051105]연교', '함량_원료성분원문': '총량 : 1회용량(2.5 g) 중|성분명 : 연교|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.5 g) 중|성분명 : 이상수침건조엑스|분량 : 1000|단위 : 밀리그램|규격 : .|성분정보 : ;총량 : 1회용량(2.5 g) 중|성분명 : 길경|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.5 g) 중|성분명 : 감초|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : 글리시리진산으로서 20.8 mg;총량 : 1회용량(2.5 g) 중|성분명 : 사인|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.5 g) 중|성분명 : 천궁|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.5 g) 중|성분명 : 가자|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.5 g) 중|성분명 : 아선약|분량 : 0.67|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.5 g) 중|성분명 : 대황|분량 : 0.33|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회용량(2.5 g) 중|성분명 : 박하|분량 : 1.33|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1회용량(2.5 g) 중', '수집URL': 'https://drug.hospitalk.net/item/200902637', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200902637', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200202807', 'ITEM_NAME': '넬리아과립(반하사심탕엑스과립)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '대추;인삼;황금;황련;감초;건강;반하', 'ENTP_NAME': '경진제약(주)', 'CHART': '황갈색의 과립제', 'CHANGE_DATE': '2009-10-07', 'BAR_CODE': '8806604009409,8806604009416,8806604009423,8806604009430,8806604009447,8806604009454,8806604009461,8806604009478,8806604009485,8806604009492,8806604026819', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040071]대추|[M051291]인삼|[M040789]황금|[M040792]황련|[M040006]감초|[M040007]건강|[M040202]반하', '함량_원료성분원문': '총량 : 전과 동일|성분명 : 반하|분량 : 1670|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 전과 동일|성분명 : 건강|분량 : 830|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 전과 동일|성분명 : 감초|분량 : 1000|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 전과 동일|성분명 : 황련|분량 : 330|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 전과 동일|성분명 : 황금|분량 : 1000|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 전과 동일|성분명 : 인삼|분량 : 1000|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 전과 동일|성분명 : 대추|분량 : 1000|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '전과 동일', '수집URL': 'https://drug.hospitalk.net/item/200202807', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200202807', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199802138', 'ITEM_NAME': '넬슨로라타딘정', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '로라타딘', 'ENTP_NAME': '한국넬슨제약(주)', 'CHART': '백색의 타원형 정제', 'CHANGE_DATE': '2020-09-03', 'BAR_CODE': '8806567002301,8806567002318,8806567002325,8806567002332,8806567002349,8806567002356,8806567002363', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M082724]로라타딘', '함량_원료성분원문': '총량 : 1정(100밀리그램)중|성분명 : 로라타딘|분량 : 10.0|단위 : 밀리그램|규격 : USP|성분정보 :', '함량_총량기준': '1정(100밀리그램)중', '수집URL': 'https://drug.hospitalk.net/item/199802138', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199802138', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199501735', 'ITEM_NAME': '넬슨이부프로펜정200밀리그램(이부프로펜)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '이부프로펜', 'ENTP_NAME': '한국넬슨제약(주)', 'CHART': '주황색의 원형 필름코팅정', 'CHANGE_DATE': '2025-10-10', 'BAR_CODE': '8806567004206,8806567004213,8806567004220,8806567004237,8806567004244', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051259]이부프로펜', '함량_원료성분원문': '총량 : 1정(255밀리그램) 중|성분명 : 이부프로펜|분량 : 200|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정(255밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/199501735', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199501735', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '199501736', 'ITEM_NAME': '넬슨이부프로펜정400밀리그램(이부프로펜)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '이부프로펜', 'ENTP_NAME': '한국넬슨제약(주)', 'CHART': '주황색의 타원형 필름코팅정', 'CHANGE_DATE': '2025-10-10', 'BAR_CODE': '8806567004305,8806567004312,8806567004329,8806567004336,8806567004343,8806567004350,8806567004367,8806567004374,8806567004381', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051259]이부프로펜', '함량_원료성분원문': '총량 : 1정(500밀리그램) 중|성분명 : 이부프로펜|분량 : 400|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1정(500밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/199501736', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=199501736', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201701092', 'ITEM_NAME': '넬케어네일라카(아모롤핀염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '아모롤핀염산염', 'ENTP_NAME': '(주)마더스제약', 'CHART': '이 약은 무색 또는 거의 무색의 투명한 액제이다.', 'CHANGE_DATE': '2021-03-16', 'BAR_CODE': '8806228029104,8806228029111', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M252763]아모롤핀염산염', '함량_원료성분원문': '총량 : 이 약 100mL 중|성분명 : 아모롤핀염산염|분량 : 5.574|단위 : 그램|규격 : EP|성분정보 : 아모롤핀으로서 5.0g', '함량_총량기준': '이 약 100mL 중', '수집URL': 'https://drug.hospitalk.net/item/201701092', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201701092', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202302141', 'ITEM_NAME': '넬클리어외용액(테르비나핀염산염)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '테르비나핀염산염', 'ENTP_NAME': '코오롱제약(주)', 'CHART': '이 약은 무색 내지 연한 황색의 투명한 액제이다.', 'CHANGE_DATE': '2023-09-11', 'BAR_CODE': '8806703048804,8806703048811,8806703048828', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M258362]테르비나핀염산염', '함량_원료성분원문': '총량 : 1밀리리터|성분명 : 테르비나핀염산염|분량 : 88.00|단위 : 밀리그램|규격 : EP|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/202302141', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202302141', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200104075', 'ITEM_NAME': '노넥스에프환(형개연교탕)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '지실;방풍;형개;연교;치자;황금;천궁;작약;시호;길경;백지;감초;당귀', 'ENTP_NAME': '경방신약(주)', 'CHART': '흑갈색의 환제', 'CHANGE_DATE': '2020-03-04', 'BAR_CODE': '8806613022208,8806613022215,8806613022222,8806613022239,8806613022246', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040536]지실|[M040205]방풍|[M051936]형개|[M051105]연교|[M040564]치자|[M040789]황금|[M040550]천궁|[M040523]작약|[M040336]시호|[M040048]길경|[M040216]백지|[M040006]감초|[M040070]당귀', '함량_원료성분원문': '총량 : 1회1.95그램|성분명 : 당귀|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회1.95그램|성분명 : 감초|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : 글리시리진산으로서 12.5mg  ;총량 : 1회1.95그램|성분명 : 백지|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회1.95그램|성분명 : 길경|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회1.95그램|성분명 : 시호|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회1.95그램|성분명 : 작약|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : 패오니플로린으로서 10.0mg;총량 : 1회1.95그램|성분명 : 천궁|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회1.95그램|성분명 : 황금|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : 바이칼린으로서 50.0mg  ;총량 : 1회1.95그램|성분명 : 치자|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : 게니포시드로서 15.0mg  ;총량 : 1회1.95그램|성분명 : 연교|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회1.95그램|성분명 : 형개|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회1.95그램|성분명 : 방풍|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회1.95그램|성분명 : 지실|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '11.95', '수집URL': 'https://drug.hospitalk.net/item/200104075', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200104075', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200005724', 'ITEM_NAME': '노넥스엑스과립(형개연교탕)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '치자;연교;형개;방풍;지실;황금;천궁;작약;시호;길경;백지;감초;당귀', 'ENTP_NAME': '경방신약(주)', 'CHART': '담황갈색의 과립제', 'CHANGE_DATE': '2020-04-13', 'BAR_CODE': '8806613022307,8806613022314', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040564]치자|[M051105]연교|[M051936]형개|[M040205]방풍|[M040536]지실|[M040789]황금|[M040550]천궁|[M040523]작약|[M040336]시호|[M040048]길경|[M040216]백지|[M040006]감초|[M040070]당귀', '함량_원료성분원문': '총량 : 1회 용량(2.5그램)중|성분명 : 당귀|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램)중|성분명 : 감초|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : 글리시리진산으로서 12.5밀리그램;총량 : 1회 용량(2.5그램)중|성분명 : 백지|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램)중|성분명 : 길경|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램)중|성분명 : 시호|분량 : 0.83|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램)중|성분명 : 작약|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : 패오니플로린으로서 10.0밀리그램;총량 : 1회 용량(2.5그램)중|성분명 : 천궁|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램)중|성분명 : 황금|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : 바이칼린으로서 50.0밀리그램;총량 : 1회 용량(2.5그램)중|성분명 : 치자|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램)중|성분명 : 연교|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램)중|성분명 : 형개|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램)중|성분명 : 방풍|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 : ;총량 : 1회 용량(2.5그램)중|성분명 : 지실|분량 : 0.5|단위 : 그램|규격 : KP|성분정보 :', '함량_총량기준': '1회 용량(2.5그램)중', '수집URL': 'https://drug.hospitalk.net/item/200005724', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200005724', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201908032', 'ITEM_NAME': '노드라나액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '글리시리진산이칼륨;알란토인;헤파리노이드', 'ENTP_NAME': '동아제약(주)', 'CHART': '유백색의 불투명한 외용액제', 'CHANGE_DATE': '2025-07-29', 'BAR_CODE': '8806265015009,8806265015016', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M256386]글리시리진산이칼륨|[M051015]알란토인|[M237233]헤파리노이드', '함량_원료성분원문': '총량 : 1그램|성분명 : 글리시리진산이칼륨|분량 : 5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1그램|성분명 : 알란토인|분량 : 2|단위 : 밀리그램|규격 : USP|성분정보 : ;총량 : 1그램|성분명 : 헤파리노이드|분량 : 3|단위 : 밀리그램|규격 : 별규|성분정보 :', '함량_총량기준': '1', '수집URL': 'https://drug.hospitalk.net/item/201908032', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201908032', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202602508', 'ITEM_NAME': '노량액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '니코틴산아미드;스코폴라민브롬화수소산염수화물;피리독신염산염;클로르페니라민말레산염;카페인무수물', 'ENTP_NAME': '(주)한풍제약', 'CHART': '갈색 또는 황갈색의 액제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806581088404,8806581088411,8806581088428', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040064]니코틴산아미드|[M223081]스코폴라민브롬화수소산염수화물|[M204304]피리독신염산염|[M223211]클로르페니라민말레산염|[M223183]카페인무수물', '함량_원료성분원문': '총량 : 1포10밀리리터|성분명 : 카페인무수물|분량 : 10.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포10밀리리터|성분명 : 클로르페니라민말레산염|분량 : 0.60|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포10밀리리터|성분명 : 피리독신염산염|분량 : 5.00|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포10밀리리터|성분명 : 스코폴라민브롬화수소산염수화물|분량 : 0.05|단위 : 밀리그램|규격 : EP|성분정보 : ;총량 : 1포10밀리리터|성분명 : 니코틴산아미드|분량 : 10.00|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '110', '수집URL': 'https://drug.hospitalk.net/item/202602508', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202602508', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '202300042', 'ITEM_NAME': '노량캡슐', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '카페인무수물;아미노벤조산에틸;피리독신염산염;스코폴라민브롬화수소산염수화물;클로르페니라민말레산염', 'ENTP_NAME': '(주)한풍제약', 'CHART': '흰색의 가루가 든 상부 연녹색, 하부 흰색의 경질캡슐', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806502060106,8806502060113,8806581087506,8806581087513,8806581087520', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M223183]카페인무수물|[M203437]아미노벤조산에틸|[M204304]피리독신염산염|[M223081]스코폴라민브롬화수소산염수화물|[M223211]클로르페니라민말레산염', '함량_원료성분원문': '총량 : 1캡슐269.0밀리그램|성분명 : 클로르페니라민말레산염|분량 : 1|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐269.0밀리그램|성분명 : 스코폴라민브롬화수소산염수화물|분량 : 0.1|단위 : 밀리그램|규격 : EP|성분정보 : ;총량 : 1캡슐269.0밀리그램|성분명 : 피리독신염산염|분량 : 2.5|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐269.0밀리그램|성분명 : 아미노벤조산에틸|분량 : 25|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1캡슐269.0밀리그램|성분명 : 카페인무수물|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1269.0', '수집URL': 'https://drug.hospitalk.net/item/202300042', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=202300042', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201402653', 'ITEM_NAME': '노루모듀얼액션현탁액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '탄산칼슘;탄산수소나트륨;알긴산나트륨', 'ENTP_NAME': '일양약품(주)', 'CHART': '페퍼민트향이 나는 미황색~크림색의 현탁액', 'CHANGE_DATE': '2015-12-17', 'BAR_CODE': '8806417046400,8806417046417,8806417046424,8806417046431,8806417046448', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M051564]탄산칼슘|[M040631]탄산수소나트륨|[M040385]알긴산나트륨', '함량_원료성분원문': '총량 : 이 약 100mL 중|성분명 : 알긴산나트륨|분량 : 5.0|단위 : 그램|규격 : EP|성분정보 : ;총량 : 이 약 100mL 중|성분명 : 탄산수소나트륨|분량 : 2.13|단위 : 그램|규격 : EP|성분정보 : ;총량 : 이 약 100mL 중|성분명 : 탄산칼슘|분량 : 3.25|단위 : 그램|규격 : EP|성분정보 :', '함량_총량기준': '이 약 100mL 중', '수집URL': 'https://drug.hospitalk.net/item/201402653', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201402653', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201506162', 'ITEM_NAME': '노루모에스산', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '용담가루;건강가루;육계가루;디아스타제·프로테아제·셀룰라제1000;감초가루;수산화마그네슘;메타규산알루민산마그네슘;탄산수소나트륨', 'ENTP_NAME': '일양약품(주)', 'CHART': '흰색과 갈색의 분말이 혼합된 산제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806417051008,8806417051015,8806417051022', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M082927]용담가루|[M082517]건강가루|[M234405]육계가루|[M261464]디아스타제·프로테아제·셀룰라제1000|[M070009]감초가루|[M040306]수산화마그네슘|[M050448]메타규산알루민산마그네슘|[M040631]탄산수소나트륨', '함량_원료성분원문': '총량 : 1포(1244.53밀리그램) 중|성분명 : 탄산수소나트륨|분량 : 400|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(1244.53밀리그램) 중|성분명 : 메타규산알루민산마그네슘|분량 : 200|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(1244.53밀리그램) 중|성분명 : 수산화마그네슘|분량 : 200|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1포(1244.53밀리그램) 중|성분명 : 감초가루|분량 : 50|단위 : 밀리그램|규격 : 생규|성분정보 : 글리시리진산으로서 1.25mg이상;총량 : 1포(1244.53밀리그램) 중|성분명 : 디아스타제·프로테아제·셀룰라제1000|분량 : 60|단위 : 밀리그램|규격 : KP|성분정보 : 전분호정화력으로서 900단위;총량 : 1포(1244.53밀리그램) 중|성분명 : 육계가루|분량 : 100|단위 : 밀리그램|규격 : 생규|성분정보 : 신남산으로서 30μg이상;총량 : 1포(1244.53밀리그램) 중|성분명 : 건강가루|분량 : 35|단위 : 밀리그램|규격 : 생규|성분정보 : ;총량 : 1포(1244.53밀리그램) 중|성분명 : 용담가루|분량 : 17|단위 : 밀리그램|규격 : 생규|성분정보 :', '함량_총량기준': '1포(1244.53밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201506162', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201506162', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201506161', 'ITEM_NAME': '노루모에이스산', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '건조수산화알루미늄겔;탄산마그네슘;탄산수소나트륨;감초가루;디아스타제·프로테아제·셀룰라제1000;침강탄산칼슘', 'ENTP_NAME': '일양약품(주)', 'CHART': '유백색의 분말로 된 산제', 'CHANGE_DATE': '미기재', 'BAR_CODE': '8806417051107,8806417051114', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M040308]건조수산화알루미늄겔|[M040629]탄산마그네슘|[M040631]탄산수소나트륨|[M070009]감초가루|[M261464]디아스타제·프로테아제·셀룰라제1000|[M040634]침강탄산칼슘', '함량_원료성분원문': '총량 : 1회(1600밀리그램) 중|성분명 : 침강탄산칼슘|분량 : 150|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회(1600밀리그램) 중|성분명 : 디아스타제·프로테아제·셀룰라제1000|분량 : 10|단위 : 밀리그램|규격 : KP|성분정보 : 전분호정화력으로서 150단위;총량 : 1회(1600밀리그램) 중|성분명 : 감초가루|분량 : 50|단위 : 밀리그램|규격 : 생규|성분정보 : 글리시리진산으로서 1.25mg이상;총량 : 1회(1600밀리그램) 중|성분명 : 탄산수소나트륨|분량 : 650|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회(1600밀리그램) 중|성분명 : 탄산마그네슘|분량 : 130|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1회(1600밀리그램) 중|성분명 : 건조수산화알루미늄겔|분량 : 270|단위 : 밀리그램|규격 : KP|성분정보 : 산화알루미늄으로서 135mg 이상', '함량_총량기준': '1회(1600밀리그램) 중', '수집URL': 'https://drug.hospitalk.net/item/201506161', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201506161', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '201404746', 'ITEM_NAME': '노루모에프내복액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '고추틴크;L-멘톨;글리신;탄산수소나트륨', 'ENTP_NAME': '일양약품(주)', 'CHART': '진갈색의 액제', 'CHANGE_DATE': '2024-04-19', 'BAR_CODE': '8806417048602,8806417048619', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M070048]고추틴크|[M279284]L-멘톨|[M088656]글리신|[M040631]탄산수소나트륨', '함량_원료성분원문': '총량 : 1병(75mL) 중|성분명 : 탄산수소나트륨|분량 : 713|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL) 중|성분명 : 글리신|분량 : 300|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL) 중|성분명 : L-멘톨|분량 : 13|단위 : 밀리그램|규격 : KP|성분정보 : ;총량 : 1병(75mL) 중|성분명 : 고추틴크|분량 : 0.033|단위 : 밀리리터|규격 : KP|성분정보 :', '함량_총량기준': '1병(75mL) 중', '수집URL': 'https://drug.hospitalk.net/item/201404746', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=201404746', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '200300960', 'ITEM_NAME': '노루모현탁액', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '보에마이트', 'ENTP_NAME': '일양약품(주)', 'CHART': '유백색의 겔상의 현탁액', 'CHANGE_DATE': '2008-03-12', 'BAR_CODE': '8806417005308,8806417005315,8806417005322,8806417005339,8806417005346', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M080685]보에마이트', '함량_원료성분원문': '총량 : 이 약 1포 (11.6그램) 중|성분명 : 보에마이트|분량 : 8.0740|단위 : 그램|규격 : 별첨규격(전과동)|성분정보 : Al2O3로서 1.212그램', '함량_총량기준': '이 약 1포 (11.6그램) 중', '수집URL': 'https://drug.hospitalk.net/item/200300960', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=200300960', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}, {'ITEM_SEQ': '198601395', 'ITEM_NAME': '노리스정(클로닉신리시네이트)', 'ETC_OTC_CODE': '일반의약품', 'MAIN_ITEM_INGR': '클로닉신리시네이트', 'ENTP_NAME': '지엘팜텍(주)', 'CHART': '노란색의 원형 필름코팅정제', 'CHANGE_DATE': '2021-05-31', 'BAR_CODE': '8806242003906,8806242003913,8806242003920,8806242003937,8806497001009,8806497001016,8806497001023,8806497001030,8806497001047,8806497001054,8806497001061,8806497001078', '허가상태_재제공자료기준': '정상', '성분_원문표기': '[M104025]클로닉신리시네이트', '함량_원료성분원문': '총량 : 1정260밀리그램|성분명 : 클로닉신리시네이트|분량 : 125|단위 : 밀리그램|규격 : KP|성분정보 :', '함량_총량기준': '1260', '수집URL': 'https://drug.hospitalk.net/item/198601395', '식약처_대조URL': 'https://nedrug.mfds.go.kr/pbp/CCBBB01/getItemDetail?itemSeq=198601395', '수집일': '2026-11-17', '검증수준': '민간 재제공 페이지 수집; 공식 서버 개별 대조·전문가 검수 전', '성분제공상태': '주성분 표기 수록; 완전성 미검증'}]

DATA_SITES = {
 "의약품안전나라 제품 검색 · 일반의약품 필터 후 엑셀 다운로드": "https://nedrug.mfds.go.kr/searchDrug",
 "식의약 데이터 포털 · 의약품 파일데이터 검색": "https://data.mfds.go.kr/",
 "공공데이터포털 · 의약품 파일데이터 검색": "https://www.data.go.kr/",
}

def safe_source_url(value):
    value = str(value or "").strip()
    parsed = urllib.parse.urlsplit(value)
    if parsed.scheme != "https" or not parsed.hostname or parsed.username or parsed.password:
        return ""
    if any(x in value for x in ("[PHONE]", "[", "]", "\n", "\r")):
        return ""
    if parsed.hostname in {"localhost", "127.0.0.1", "169.254.169.254"}:
        return ""
    return value


def snapshot_details(code):
    row = next((x for x in st.session_state.get("snapshot_rows", []) if x["ITEM_SEQ"] == code), None)
    if row is None:
        raise ApiError("업로드 자료에서 품목을 찾지 못했습니다. 다시 검색하세요.")
    ingredients, complete = parse_active_names(row.get("MAIN_ITEM_INGR", ""))
    return {"product": row, "ingredients": ingredients, "ingredient_complete": complete,
        "warnings": ["교육용 스냅샷: 민간 재제공 자료이며 공식 원문 개별 대조·전체 성분 완전성 검수 전입니다. 포장과 대조하세요.",
                     "이 파일에는 공식 DUR 병용금기 전체가 없습니다. 미검출은 안전 판정이 아닙니다."],
        "leaflet": {}, "dur": [], "dur_complete": False, "elderly": [],
        "elderly_complete": False, "fetched_at": st.session_state.get("snapshot_date", "미상")}


def offline_data_panel():
    import pandas as pd
    st.markdown("### 📚 학습용 일반의약품 자료실")
    st.success(f"현재 {len(st.session_state.get('snapshot_rows', [])):,}품목 로드됨 · 기본 506품목 내장 · API 키 불필요")
    st.caption("제품명순 일부 품목입니다. 모든 브랜드·모든 질환을 포괄하지 않습니다. 주성분 별칭·염·수화물 통합 검수 전이며 미검색/미검출은 안전을 뜻하지 않습니다.")
    if st.button("기본 506품목으로 복원"):
        st.session_state.snapshot_rows = copy.deepcopy(BUILTIN_OTC_ROWS)
        st.session_state.snapshot_source = "https://drug.hospitalk.net/item"
        st.session_state.snapshot_date = BUILTIN_OTC_ROWS[0].get("수집일", "미상")
        st.session_state.search_results = None
        st.session_state.pending_med = None
        invalidate_report()
        st.success("기본 교육 자료로 복원했습니다.")
    st.info("학습목표: ① 상품명과 성분명 구별 ② 복합제 중복 찾기 ③ 미확인을 안전과 구별하기. 처방 적합성·복용량 판단은 하지 않습니다.")
    for label, url in DATA_SITES.items():
        st.link_button(label, url)
    st.caption("의약품안전나라에서 일반의약품으로 검색 후 엑셀 다운로드를 이용하세요. 사이트 개편·검색 조건에 따라 다운로드 제공 범위는 달라질 수 있습니다. e약은요 요약자료만으로는 전체 유효성분을 확인하지 못할 수 있습니다.")
    sample = "품목기준코드,제품명,전문일반,업체명,주성분,제형,변경일자\nEDU001,가상 학습용 진통제,일반의약품,교육예제,아세트아미노펜,정제,교육예제\nEDU002,가상 학습용 복합감기약,일반의약품,교육예제,아세트아미노펜;클로르페니라민말레산염,정제,교육예제\n"
    st.download_button("교육용 CSV 양식 받기 · 실제 제품 아님", sample.encode("utf-8-sig"), "교육용_양식.csv", "text/csv")
    up = st.file_uploader("Excel(.xlsx) 또는 CSV 업로드 · 최대 20MB", type=["xlsx", "csv"], key="offline_upload")
    if not up:
        return
    if up.size > 20 * 1024 * 1024:
        st.error("20MB 이하 파일을 사용하세요."); return
    try:
        if up.name.lower().endswith("xlsx"):
            book = pd.ExcelFile(io.BytesIO(up.getvalue()), engine="openpyxl")
            sheet = st.selectbox("시트 선택", book.sheet_names)
            df = pd.read_excel(book, sheet_name=sheet, dtype=str, nrows=50001).fillna("")
        else:
            try:
                df = pd.read_csv(io.BytesIO(up.getvalue()), dtype=str, encoding="utf-8-sig", nrows=50001).fillna("")
            except UnicodeDecodeError:
                df = pd.read_csv(io.BytesIO(up.getvalue()), dtype=str, encoding="cp949", nrows=50001).fillna("")
        if len(df) > 50000 or df.empty:
            st.error("1~50,000행 파일만 지원합니다."); return
        df.columns = [str(c).strip() for c in df.columns]
        if len(set(df.columns)) != len(df.columns):
            st.error("중복 열 이름을 정리하세요."); return
        st.dataframe(df.head(5), hide_index=True)
        aliases = {"ITEM_SEQ":["ITEM_SEQ","품목기준코드"],"ITEM_NAME":["ITEM_NAME","제품명","품목명"],
          "ETC_OTC_CODE":["ETC_OTC_CODE","전문일반","전문/일반","전문일반구분"],
          "MAIN_ITEM_INGR":["MAIN_ITEM_INGR","주성분","유효성분"],"ENTP_NAME":["ENTP_NAME","업체명","제조사"],
          "CHART":["CHART","제형","성상"],"CHANGE_DATE":["CHANGE_DATE","변경일자"],"BAR_CODE":["BAR_CODE","바코드"]}
        cols = ["미제공"] + list(df.columns); mapped = {}
        for field, options in aliases.items():
            found = next((c for c in options if c in df.columns), "미제공")
            mapped[field] = st.selectbox(field + " 열 연결", cols, index=cols.index(found), key="map_"+field)
        st.warning("주성분 열은 첨가제가 섞이지 않은 '전체 유효성분명'이어야 합니다. 구분자는 세미콜론(;)을 권장합니다. 원료약품 전체·효능·주의 문장을 주성분 열에 연결하지 마세요. 코드 1/2는 자동 해석하지 않습니다.")
        source = st.text_input("원본 출처 HTTPS 주소 · 없으면 비워두세요", key="snapshot_source_input")
        day = st.date_input("원본 파일 다운로드 날짜")
        confirmed = st.checkbox("분류 열의 일반의약품 표시와 유효성분 열의 의미를 원본과 대조했습니다")
        if st.button("자료 적용", type="primary"):
            if mapped["ITEM_NAME"] == "미제공" or mapped["ETC_OTC_CODE"] == "미제공" or not confirmed:
                st.error("제품명·전문일반 열과 대조 확인이 필요합니다."); return
            records=[]; ids=set(); excluded=0
            for idx, row in df.iterrows():
                record={k: (str(row[c]).strip() if c != "미제공" else "") for k,c in mapped.items()}
                if record["ETC_OTC_CODE"] not in ("일반", "일반의약품") or not record["ITEM_NAME"]:
                    excluded+=1; continue
                code=record["ITEM_SEQ"] or "LOCAL-"+str(idx)
                if code in ids:
                    st.error("품목코드 중복이 있습니다. 동일 품목의 성분별 여러 행은 한 행으로 정리한 후 업로드하세요."); return
                ids.add(code);record["ITEM_SEQ"]=code;records.append(record)
            if not records:
                st.error("명시적으로 일반/일반의약품으로 분류된 행이 없습니다.");return
            st.session_state.snapshot_rows=records
            st.session_state.snapshot_source=safe_source_url(source)
            st.session_state.snapshot_date=str(day)
            st.session_state.search_results=None;st.session_state.pending_med=None
            st.session_state.open_search=False
            invalidate_report()
            st.success(f"일반의약품 {len(records):,}개 적용 · 제외 {excluded:,}개. 자료는 현재 세션에서만 유지됩니다. 창을 닫고 검색하세요.")

    except Exception:
        st.error("파일을 읽지 못했습니다. 암호 없는 xlsx/CSV와 열 구성을 확인하세요.")

def api_search(query, key, barcode=False, page=1):
    query = text_value(query)

    try:
        page = int(page)
    except (ValueError, TypeError):
        raise ApiError("검색 페이지 형식이 올바르지 않습니다.") from None

    if not 1 <= page <= 1000:
        raise ApiError("검색 페이지 범위를 확인해 주세요.")

    if barcode:
        query = re.sub(r"\s", "", query)

        if not re.fullmatch(r"\d{13}", query):
            raise ApiError(
                "의약품 포장의 13자리 표준코드를 입력해 주세요."
            )

        field = "bar_code"
    else:
        query = unicodedata.normalize("NFKC", query)
        query = re.sub(r"[^가-힣A-Za-z0-9\s]", " ", query)
        query = re.sub(r"\s+", " ", query).strip()
        if not 2 <= len(query) <= 80 or not re.search(r"[가-힣A-Za-z]", query):
            raise ApiError(
                "약 이름을 2~80자로 입력해 주세요. 예: 타이레놀, 하벤"
            )

        field = "item_name"

    if st.session_state.get("snapshot_rows"):
        rows = st.session_state.snapshot_rows
        def matches(row):
            if barcode:
                return query in re.split(r"[;,|\s]+", row.get("BAR_CODE", ""))
            name = re.sub(r"\s+", "", unicodedata.normalize("NFKC", row.get("ITEM_NAME", ""))).casefold()
            return all(token.casefold() in name for token in query.split())
        found = [row for row in rows if matches(row)]
        return {"items": found[(page-1)*10:page*10], "total": len(found), "page": page,
                "fetched_at": st.session_state.get("snapshot_date", "미상")}

    items, total = api_get(
        PERMIT_BASE,
        "getDrugPrdtPrmsnDtlInq08",
        key,
        {field: query, "etc_otc_code": "일반의약품"},
        page=page,
        rows=10,
    )

    return {
        "items": items,
        "total": total,
        "page": page,
        "fetched_at": api_now(),
    }


def ingredient_name_key(name):
    return re.sub(
        r"\s+",
        "",
        unicodedata.normalize("NFKC", str(name)),
    ).casefold()


def parse_active_names(raw):
    """
    유효성분 필드 MAIN_ITEM_INGR만 사용합니다.
    INGR_NAME은 첨가제 필드이므로 사용하지 않습니다.
    불명확한 직렬화 형식은 완전한 성분 목록으로 확정하지 않습니다.
    """
    raw = html.unescape(text_value(raw)).strip()

    if not raw:
        return [], False

    result = []
    complete = True
    coded = list(re.finditer(r"\[([A-Za-z]\d{4,12})\]", raw))

    if coded:
        if raw[:coded[0].start()].strip(" ;|,/"):
            complete = False

        for index, token in enumerate(coded):
            end = (
                coded[index + 1].start()
                if index + 1 < len(coded)
                else len(raw)
            )
            name = raw[token.end():end].strip(" ;|,/")

            if not name or re.search(r"[|;\n\[\]]", name):
                complete = False
                continue

            result.append({
                "name": name,
                "amount": "",
                "code": token.group(1),
            })
    else:
        if any(mark in raw for mark in (",", "，", "/")):
            return [], False

        for part in re.split(r"[|;\n]+", raw):
            name = part.strip()

            if (
                not name
                or len(name) > 150
                or re.search(r"[<>\[\]]", name)
            ):
                complete = False
                continue

            result.append({
                "name": name,
                "amount": "",
                "code": "",
            })

    dedup = {}

    for item in result:
        if re.search(r"[=:]|성분명|분량\s*:", item["name"]):
            complete = False
            continue

        dedup.setdefault(ingredient_name_key(item["name"]), item)

    return list(dedup.values()), bool(dedup) and complete


def check_item_rows(rows, item_seq):
    for row in rows:
        returned = text_value(
            row.get("ITEM_SEQ", row.get("itemSeq"))
        )
        if returned != item_seq:
            raise ApiError(
                "공식 API의 품목코드가 요청한 제품과 일치하지 않습니다."
            )

    return rows


def api_details(item_seq, key):
    item_seq = text_value(item_seq)
    if st.session_state.get("snapshot_rows"):
        return snapshot_details(item_seq)

    if not re.fullmatch(r"\d{9}", item_seq):
        raise ApiError("공식 품목기준코드를 확인해 주세요.")

    products, _ = api_get(
        PERMIT_BASE,
        "getDrugPrdtPrmsnDtlInq08",
        key,
        {"item_seq": item_seq},
        rows=10,
    )

    products = check_item_rows(products, item_seq)

    if len(products) != 1:
        raise ApiError(
            "해당 품목의 공식 상세정보를 하나로 확인하지 못했습니다."
        )

    product = products[0]
    warnings = []

    ingredients, complete = parse_active_names(
        product.get("MAIN_ITEM_INGR")
    )

    if not complete:
        warnings.append(
            "공식 유효성분 전체를 자동 확인하지 못했습니다. "
            "포장·공식 원문으로 성분을 확인해 주세요."
        )

    if ingredients:
        try:
            raw_ingredients = api_all(
                PERMIT_BASE,
                "getDrugPrdtMcpnDtlInq08",
                key,
                {"Item_seq": item_seq},
                max_pages=5,
            )

            raw_ingredients = check_item_rows(
                raw_ingredients,
                item_seq,
            )

            for active in ingredients:
                matches = [
                    row
                    for row in raw_ingredients
                    if ingredient_name_key(
                        text_value(row.get("MTRAL_NM"))
                    ) == ingredient_name_key(active["name"])
                ]

                quantities = {
                    (
                        text_value(row.get("QNT")),
                        text_value(row.get("INGD_UNIT_CD")),
                        text_value(row.get("TAMT_SEQ")),
                    )
                    for row in matches
                }

                if len(quantities) == 1:
                    qty, unit, group = next(iter(quantities))

                    if qty:
                        active["amount"] = qty + (
                            " " + unit
                            if unit
                            else " (단위 미확인)"
                        )

                        if group:
                            active["amount"] += " · 총량그룹 " + group

                if not active["code"] and matches:
                    codes = {
                        text_value(row.get("MTRAL_CODE"))
                        for row in matches
                    }
                    if len(codes) == 1:
                        active["code"] = next(iter(codes))

        except ApiError as exc:
            warnings.append("함량 보강 조회 미완료: " + str(exc))

    leaflet = {}

    try:
        leaves, _ = api_get(
            EASY_BASE,
            "getDrbEasyDrugList",
            key,
            {"itemSeq": item_seq},
            rows=10,
        )

        leaves = check_item_rows(leaves, item_seq)

        if len(leaves) == 1:
            leaflet = leaves[0]
        elif len(leaves) > 1:
            warnings.append(
                "e약은요 자료가 여러 건이라 자동 연결하지 않았습니다."
            )
        else:
            warnings.append(
                "이 품목에는 e약은요 자료가 없습니다."
            )

    except ApiError as exc:
        warnings.append("e약은요 조회 미완료: " + str(exc))

    result = {
        "product": product,
        "ingredients": ingredients,
        "ingredient_complete": complete,
        "warnings": warnings,
        "leaflet": leaflet,
        "dur": [],
        "dur_complete": False,
        "elderly": [],
        "elderly_complete": False,
        "fetched_at": api_now(),
    }

    endpoints = [
        (
            "병용금기",
            "getUsjntTabooInfoList03",
            "dur",
            "dur_complete",
        ),
        (
            "노인주의",
            "getOdsnAtentInfoList03",
            "elderly",
            "elderly_complete",
        ),
    ]

    for label, operation, list_key, done_key in endpoints:
        try:
            rows = api_all(
                DUR_BASE,
                operation,
                key,
                {"itemSeq": item_seq},
            )
            result[list_key] = check_item_rows(rows, item_seq)
            result[done_key] = True

        except ApiError as exc:
            warnings.append(label + " 조회 미완료: " + str(exc))

    return result


def official_item_to_med(detail):
    product = detail["product"]
    item_seq = text_value(product.get("ITEM_SEQ"))
    classification = text_value(product.get("ETC_OTC_CODE"))

    if "일반" in classification:
        kind = "일반의약품"
    elif "전문" in classification:
        kind = "처방의약품"
    else:
        kind = "미확인"

    return {
        "id": item_seq,
        "name": text_value(product.get("ITEM_NAME")),
        "kind": kind,
        "form": text_value(product.get("CHART")),
        "manufacturer": text_value(product.get("ENTP_NAME")),
        "ingredients": detail["ingredients"],
        "confirmed": True,
        "origin": "snapshot" if st.session_state.get("snapshot_rows") else "official",
        "source_url": product.get("수집URL") or st.session_state.get("snapshot_source", "") if st.session_state.get("snapshot_rows") else item_url(item_seq),
        "source_date": text_value(product.get("CHANGE_DATE")),
        "dur": detail["dur"],
        "dur_complete": detail["dur_complete"],
        "elderly": detail["elderly"],
        "elderly_complete": detail["elderly_complete"],
        "leaflet": detail["leaflet"],
        "warnings": detail["warnings"],
        "ingredient_complete": detail["ingredient_complete"],
        "fetched_at": detail["fetched_at"],
        "status": text_value(product.get("CANCEL_NAME")),
        "raw_ingredients": text_value(
            product.get("MAIN_ITEM_INGR")
        ),
        "raw_material": text_value(product.get("MATERIAL_NAME")),
        "official_warning_text": (
            text_value(product.get("NB_DOC_DATA"))
            or text_value(product.get("PN_DOC_DATA"))
        ),
        "barcodes": text_value(product.get("BAR_CODE")),
    }


# ============================================================
# 성분 정규화 및 근거 기반 분석
# ============================================================

def alias_key(value):
    value = unicodedata.normalize(
        "NFKC",
        str(value or ""),
    ).strip().casefold()

    return re.sub(r"[\s·_\-]+", "", value)


ALIAS_GROUPS = {
    "아세트아미노펜": [
        "acetaminophen", "paracetamol",
        "아세트아미노펜(KP)", "아세트아미노펜(USP)",
    ],
    "클로르페니라민": [
        "chlorpheniramine", "chlorphenamine",
        "chlorpheniramine maleate", "chlorphenamine maleate",
        "클로르페니라민말레산염", "말레인산클로르페니라민",
    ],
    "디펜히드라민": [
        "diphenhydramine", "diphenhydramine hydrochloride",
        "디펜히드라민염산염", "염산디펜히드라민",
    ],
    "이부프로펜": ["ibuprofen"],
    "덱시부프로펜": ["dexibuprofen"],
    "나프록센": ["naproxen", "naproxen sodium", "나프록센나트륨"],
    "디클로페낙": [
        "diclofenac", "diclofenac sodium", "diclofenac potassium",
        "디클로페낙나트륨", "디클로페낙칼륨",
    ],
    "아세클로페낙": ["aceclofenac"],
    "셀레콕시브": ["celecoxib"],
    "아스피린": ["aspirin", "acetylsalicylic acid", "아세틸살리실산"],
    "슈도에페드린": [
        "pseudoephedrine", "pseudoephedrine hydrochloride",
        "슈도에페드린염산염", "염산슈도에페드린",
    ],
    "메트포르민": [
        "metformin", "metformin hydrochloride",
        "메트포르민염산염", "염산메트포르민",
    ],
    "글리메피리드": ["glimepiride"],
    "글리클라지드": ["gliclazide"],
    "글리벤클라미드": ["glibenclamide", "glyburide"],
    "글리피지드": ["glipizide"],
    "인슐린인체": [
        "human insulin", "insulin human",
        "Human Insulin (Recombinant)",
        "사람인슐린", "휴먼인슐린",
        "휴먼인슐린(유전자재조합)",
        "인슐린(유전자재조합)",
        "인슐린인체(유전자재조합)",
    ],
    "인슐린글라진": [
        "insulin glargine", "인슐린글라진(유전자재조합)",
    ],
    "인슐린아스파트": [
        "insulin aspart", "인슐린아스파트(유전자재조합)",
    ],
    "인슐린리스프로": [
        "insulin lispro", "인슐린리스프로(유전자재조합)",
    ],
    "인슐린데글루덱": [
        "insulin degludec", "인슐린데글루덱(유전자재조합)",
    ],
    "인슐린데테미르": [
        "insulin detemir", "인슐린데테미르(유전자재조합)",
    ],
    "인슐린글루리신": [
        "insulin glulisine", "인슐린글루리신(유전자재조합)",
    ],
    "프로프라놀롤": [
        "propranolol", "propranolol hydrochloride",
        "프로프라놀롤염산염",
    ],
    "아테놀롤": ["atenolol"],
    "비소프롤롤": [
        "bisoprolol", "bisoprolol fumarate",
        "비소프롤롤푸마르산염",
    ],
    "카르베딜롤": ["carvedilol"],
    "메토프롤롤": [
        "metoprolol", "metoprolol tartrate", "metoprolol succinate",
        "메토프롤롤타르타르산염", "메토프롤롤숙신산염",
    ],
    "심바스타틴": ["simvastatin"],
    "레보티록신": [
        "levothyroxine", "levothyroxine sodium",
        "레보티록신나트륨", "레보티록신나트륨수화물",
    ],
    "탄산칼슘": ["calcium carbonate", "침강탄산칼슘"],
    "황산철": [
        "ferrous sulfate", "ferrous sulphate",
        "황산제일철", "건조황산제일철",
    ],
    "와파린": ["warfarin", "warfarin sodium", "와파린나트륨"],
    "아픽사반": ["apixaban"],
    "리바록사반": ["rivaroxaban"],
    "다비가트란에텍실레이트": [
        "dabigatran etexilate", "dabigatran etexilate mesylate",
        "다비가트란에텍실레이트메실산염",
    ],
}

ALIASES = {
    alias_key(alias): canonical
    for canonical, aliases in ALIAS_GROUPS.items()
    for alias in [canonical] + aliases
}

INSULINS = {
    "인슐린인체", "인슐린글라진", "인슐린아스파트",
    "인슐린리스프로", "인슐린데글루덱",
    "인슐린데테미르", "인슐린글루리신",
}

SULFONYL = {
    "글리메피리드", "글리클라지드",
    "글리벤클라미드", "글리피지드",
}

NSAIDS = {
    "이부프로펜", "덱시부프로펜", "나프록센",
    "디클로페낙", "아세클로페낙", "셀레콕시브", "아스피린",
}

BETA_BLOCKERS = {
    "프로프라놀롤", "아테놀롤", "비소프롤롤",
    "카르베딜롤", "메토프롤롤",
}

ANTICOAGULANTS = {
    "와파린", "아픽사반", "리바록사반",
    "다비가트란에텍실레이트",
}

ANTICHOLINERGICS = {
    "디펜히드라민", "클로르페니라민",
}


def normalize_ingredient(value):
    original = " ".join(
        unicodedata.normalize(
            "NFKC",
            str(value or ""),
        ).strip().split()
    )

    return ALIASES.get(alias_key(original), original)


def official_item_seq(med):
    if med.get("origin") != "official" or not med.get("confirmed"):
        return ""

    value = str(
        med.get("item_seq")
        or med.get("ITEM_SEQ")
        or med.get("id")
        or ""
    )

    value = re.sub(r"^(?:mfds|official):", "", value)

    return value if re.fullmatch(r"\d{8,12}", value) else ""


def list_rows(value):
    if isinstance(value, dict):
        return [value]
    if isinstance(value, list):
        return value
    return []


def analyze(meds, candidate, conditions, older, foods=None):
    foods = list(foods or [])
    conditions = set(conditions or [])

    unique = {}

    for index, med in enumerate(meds or []):
        if isinstance(med, dict):
            unique.setdefault(
                str(med.get("id") or f"row-{index}"),
                med,
            )

    products = list(unique.values())
    findings = []
    emitted = set()

    def add(
        level,
        title,
        detail,
        action,
        source,
        scope="general",
        selected=None,
        mechanism="",
    ):
        ids = list(dict.fromkeys(
            str(m.get("id") or m.get("name") or "")
            for m in (selected or [])
        ))

        key = (level, title, tuple(sorted(ids)))

        if key in emitted:
            return

        emitted.add(key)

        finding = {
            "level": level,
            "title": title,
            "detail": detail,
            "action": action,
            "source": source,
            "scope": scope,
            "med_ids": ids,
        }

        if mechanism:
            finding["mechanism"] = mechanism

        findings.append(finding)

    if isinstance(candidate, dict):
        matching = next(
            (
                m for m in products
                if m.get("id")
                and str(m["id"]) == str(candidate.get("id"))
            ),
            None,
        )

        if matching:
            add(
                "duplicate",
                "복용 중인 제품과 같은 구매 예정 품목",
                (
                    f"{candidate.get('name', '제품')}이 복용 목록과 "
                    "구매 예정에 함께 등록되어 있습니다."
                ),
                "실제 추가 복용 계획인지 약사와 확인하세요.",
                SOURCES["mfds"],
                "data",
                [matching, candidate],
            )
        else:
            products.append(candidate)

    if not products:
        return [{
            "level": "unknown",
            "title": "점검할 약을 등록해 주세요",
            "detail": (
                "정확한 제품·제형·함량을 선택하고 "
                "복용 목록과 구매 예정 약을 등록해야 점검할 수 있습니다."
            ),
            "action": "건강기능식품과 필요할 때만 먹는 약도 알려주세요.",
            "source": SOURCES["mfds"],
            "scope": "data",
            "med_ids": [],
        }]

    known = []
    ingredient_owners = defaultdict(list)

    for med in products:
        name = str(med.get("name") or "이름 미등록 제품")

        if not med.get("confirmed"):
            add(
                "unknown",
                f"제품 확인 필요 · {name}",
                (
                    "제품명·제형·함량·성분이 아직 확인되지 않았습니다. "
                    "이 제품은 성분 기반 분석에서 제외했습니다."
                ),
                "포장이나 처방전과 비교해 확인하세요.",
                SOURCES["mfds"],
                "data",
                [med],
            )
            continue

        ingredients = {
            normalize_ingredient(i.get("name", ""))
            for i in med.get("ingredients", [])
            if isinstance(i, dict) and i.get("name")
        }

        known.append((med, ingredients))

        if not med.get("ingredient_complete") or not ingredients:
            add(
                "unknown",
                f"성분 정보 불완전 · {name}",
                (
                    "확인된 일부 성분만 점검했습니다. "
                    "누락된 성분의 중복·상호작용은 평가하지 못했습니다."
                ),
                "공식 성분표 전체와 함량·단위를 확인하세요.",
                SOURCES["mfds"],
                "data",
                [med],
            )

        for ingredient in ingredients:
            ingredient_owners[ingredient].append(med)

    for ingredient, owners in ingredient_owners.items():
        if len(owners) < 2:
            continue

        names = " / ".join(
            str(m.get("name", "제품")) for m in owners
        )

        if ingredient in INSULINS:
            note = (
                " 인슐린은 농도·혼합비·작용시간이 달라 "
                "교환하거나 용량을 환산할 수 없습니다."
            )
            source = SOURCES["insulin"]
        else:
            note = (
                " 제형·함량·투여 경로를 함께 확인해야 하며 "
                "이 결과는 과량 복용 판정이 아닙니다."
            )
            source = (
                SOURCES["acetaminophen"]
                if ingredient == "아세트아미노펜"
                else SOURCES["mfds"]
            )

        add(
            "duplicate",
            f"동일 성분 겹침 · {ingredient}",
            f"{names}에 같은 성분으로 확인된 명칭이 있습니다.{note}",
            (
                "기존 처방약을 임의로 중단하지 말고, "
                "새 약의 추가 복용 여부와 총량을 약사에게 확인하세요."
            ),
            source,
            "data",
            owners,
        )

    # 공식 금기는 정확한 품목 코드 두 개와 금기 원문이 있을 때만 표시.
    for med, other in combinations(products, 2):
        left = official_item_seq(med)
        right = official_item_seq(other)

        if not left or not right:
            continue

        for owner, own_id, target_id in (
            (med, left, right),
            (other, right, left),
        ):
            for row in list_rows(owner.get("dur")):
                if not isinstance(row, dict):
                    continue

                if (
                    str(row.get("ITEM_SEQ", "")).strip() != own_id
                    or str(
                        row.get("MIXTURE_ITEM_SEQ", "")
                    ).strip() != target_id
                ):
                    continue

                reason = str(
                    row.get("PROHBT_CONTENT") or ""
                ).strip()

                if not reason:
                    continue

                add(
                    "contraindication",
                    (
                        f"공식 병용금기 · {med.get('name', '제품')} "
                        f"+ {other.get('name', '제품')}"
                    ),
                    reason,
                    (
                        "추가 병용 전에 약사·처방의에게 공식 금기 사유를 "
                        "보여주세요. 기존 약의 중단·대체·용량 변경은 "
                        "전문가가 결정합니다."
                    ),
                    item_url(own_id),
                    "official",
                    [med, other],
                )

    incomplete_dur = [
        m for m in products
        if not m.get("dur_complete") or not official_item_seq(m)
    ]

    if incomplete_dur:
        add(
            "unknown",
            "공식 병용금기 점검 미완료",
            (
                "다음 제품의 국내 DUR 조회 또는 공식 품목 확인이 "
                "완료되지 않았습니다: "
                + ", ".join(m.get("name", "제품") for m in incomplete_dur)
                + ". 조회 실패·자료 없음은 병용 가능하다는 뜻이 아닙니다."
            ),
            "공식 품목을 확인하고 전체 목록을 약사에게 보여주세요.",
            SOURCES["mfds"],
            "data",
            incomplete_dur,
        )

    if older:
        missing_elderly = []

        for med in products:
            seq = official_item_seq(med)

            if not med.get("elderly_complete") or not seq:
                missing_elderly.append(med)

            for row in list_rows(med.get("elderly")):
                if (
                    not isinstance(row, dict)
                    or not seq
                    or str(row.get("ITEM_SEQ", "")).strip() != seq
                ):
                    continue

                reason = str(
                    row.get("PROHBT_CONTENT") or ""
                ).strip()

                if reason:
                    add(
                        "caution",
                        f"공식 노인주의 · {med.get('name', '제품')}",
                        reason,
                        (
                            "연령·낙상·인지·신장 기능과 함께 "
                            "약사·처방의에게 확인하세요."
                        ),
                        item_url(seq),
                        "official",
                        [med],
                    )

        if missing_elderly:
            add(
                "unknown",
                "공식 노인주의 점검 미완료",
                "일부 제품의 공식 노인주의 자료가 확인되지 않았습니다.",
                "수면보조제와 일반약을 포함해 약사에게 확인하세요.",
                SOURCES["mfds"],
                "data",
                missing_elderly,
            )

    def owners(group):
        return [
            med for med, ingredients in known
            if ingredients & group
        ]

    all_ingredients = (
        set().union(*(ingredients for _, ingredients in known))
        if known else set()
    )

    nsaids = owners(NSAIDS)
    antichol = owners(ANTICHOLINERGICS)
    hypoglycemic = owners(INSULINS | SULFONYL)

    for med1, med2 in combinations(nsaids, 2):
        first = next(
            ingredients for med, ingredients in known if med is med1
        ) & NSAIDS
        second = next(
            ingredients for med, ingredients in known if med is med2
        ) & NSAIDS

        if first != second or len(first | second) > 1:
            add(
                "caution",
                "같은 계열 진통소염제 겹침",
                (
                    "서로 다른 NSAID 성분이 등록되어 있습니다. "
                    "같은 성분 중복과 별개로 위장관 출혈·신장 "
                    "부작용을 검토해야 합니다."
                ),
                (
                    "국소제·먹는 약의 경로를 알려주세요. "
                    "저용량 아스피린 처방은 임의로 중단하지 마세요."
                ),
                SOURCES["nsaid"],
                selected=[med1, med2],
            )

    anticoag = owners(ANTICOAGULANTS)

    if nsaids and anticoag:
        add(
            "caution",
            "항응고제와 진통소염제 · 출혈 위험 확인",
            "항응고제와 NSAID 조합은 출혈 위험에 영향을 줄 수 있습니다.",
            (
                "항응고제를 임의로 중단하지 말고 "
                "새 진통제 구매 전에 상담하세요."
            ),
            SOURCES["warfarin"],
            selected=nsaids + anticoag,
            mechanism=(
                "약력학적 주의: 응고·혈소판 및 위장관 손상과 "
                "관련된 출혈 위험입니다. ADME 기전으로 분류하지 않습니다."
            ),
        )

    if nsaids and conditions & {"당뇨병", "고혈압", "만성콩팥병"}:
        add(
            "caution",
            "진통소염제 · 신장·혈압 상태 확인",
            (
                "당뇨병·고혈압·만성콩팥병과 탈수는 NSAID 사용 시 "
                "신장 위험을 검토해야 하는 요인입니다."
            ),
            "최근 신장 검사와 탈수 여부를 알려 구매 전 상담하세요.",
            SOURCES["kidney"],
            selected=nsaids,
        )

    if nsaids and "심부전" in conditions:
        add(
            "caution",
            "심부전 · 진통소염제 추가 전 확인",
            "NSAID는 체액 저류와 심부전 악화에 영향을 줄 수 있습니다.",
            "새 진통제 사용 전에 심부전 치료팀에 확인하세요.",
            SOURCES["heart"],
            selected=nsaids,
        )

    if nsaids and "위궤양·위장출혈 병력" in conditions:
        add(
            "caution",
            "출혈 병력 · 진통소염제 확인",
            (
                "NSAID의 위장관 출혈 위험은 고령·과거 궤양·"
                "출혈·동반약에 따라 달라집니다."
            ),
            "과거 출혈·궤양과 현재 항혈전제를 알려주세요.",
            SOURCES["nsaid"],
            selected=nsaids,
        )

    if nsaids and "천식" in conditions:
        add(
            "caution",
            "천식 · 진통소염제 반응 병력 확인",
            (
                "일부 환자는 아스피린·NSAID 사용 후 "
                "호흡기 증상이 악화될 수 있습니다. "
                "천식 전체에 대한 절대금기 판정은 아닙니다."
            ),
            "진통소염제로 숨참·천식 악화가 있었는지 알려주세요.",
            SOURCES["asthma"],
            selected=nsaids,
        )

    pseudo = owners({"슈도에페드린"})

    if pseudo and conditions & {
        "당뇨병", "고혈압", "심부전", "녹내장·배뇨장애",
    }:
        add(
            "caution",
            "코막힘 성분 · 기저질환 확인",
            (
                "슈도에페드린은 혈압·심장·당뇨병·녹내장·"
                "배뇨장애 병력에 따라 사용 전 확인이 필요합니다."
            ),
            "질환 조절 상태와 정확한 진단 유형을 알려주세요.",
            SOURCES["pseudo"],
            selected=pseudo,
        )

    if antichol and (older or "인지저하·치매" in conditions):
        add(
            "caution",
            "항콜린성 성분 · 졸림·혼동 확인",
            (
                "일부 1세대 항히스타민은 고령자·인지저하 환자에서 "
                "졸림·혼동 등 부작용을 검토해야 합니다. "
                "치매의 원인이나 악화를 확정하는 결과는 아닙니다."
            ),
            "감기약·알레르기약·수면보조제를 함께 제시하세요.",
            SOURCES["cognition"],
            selected=antichol,
        )

    if antichol and "녹내장·배뇨장애" in conditions:
        add(
            "caution",
            "항히스타민 · 눈·배뇨 상태 확인",
            (
                "항콜린성 성분은 특히 폐쇄각녹내장·전립선비대 "
                "등의 병력에서 주의가 필요합니다."
            ),
            "녹내장 종류와 배뇨장애를 알려 구매 전 상담하세요.",
            SOURCES["anticholinergic"],
            selected=antichol,
        )

    if hypoglycemic:
        add(
            "caution",
            "인슐린·일부 혈당강하제 · 식사와 저혈당",
            (
                "등록된 인슐린 또는 설포닐유레아는 결식·식사 지연·"
                "섭취량 감소·음주와 함께 저혈당 위험을 검토해야 합니다. "
                "메트포르민 단독은 이 규칙에 포함하지 않습니다."
            ),
            (
                "식사·혈당 확인 계획을 따르고 식사량이 달라졌을 때의 "
                "대처를 치료팀에 확인하세요. 용량은 임의 변경하지 마세요."
            ),
            SOURCES["hypo"],
            selected=hypoglycemic,
        )

        beta = owners(BETA_BLOCKERS)

        if beta:
            add(
                "caution",
                "베타차단제 병용 · 저혈당 자각 증상 확인",
                (
                    "일부 베타차단제는 저혈당을 "
                    "알아차리기 어렵게 할 수 있습니다."
                ),
                (
                    "증상만으로 판단하지 말고 혈당 확인 계획을 상담하세요. "
                    "심장약을 임의로 중단하지 마세요."
                ),
                SOURCES["beta"],
                selected=hypoglycemic + beta,
            )

    insulin = owners(INSULINS)

    if len(insulin) > 1:
        add(
            "caution",
            "인슐린 종류·농도 · 처방 구성 확인",
            (
                "기저·식사 인슐린 병용은 처방된 구성일 수 있습니다. "
                "다른 작용시간·농도·혼합비를 같은 제품으로 취급하지 "
                "않으며 중복 처방을 확정하지 않습니다."
            ),
            "제품명·농도·기기·투여 계획을 약사에게 보여주세요.",
            SOURCES["insulin"],
            selected=insulin,
        )

    if (
        "레보티록신" in all_ingredients
        and all_ingredients & {"탄산칼슘", "황산철"}
    ):
        add(
            "caution",
            "갑상선호르몬·칼슘/철 · 흡수 확인",
            (
                "미국 허가문서에는 레보티록신과 탄산칼슘·황산철의 "
                "흡수 영향 및 복용 간격 안내가 있습니다. "
                "한국의 실제 제품 허가사항을 우선 확인하세요."
            ),
            "현재 복용 시각을 약사에게 보여 적절한 간격을 확인하세요.",
            SOURCES["thyroid"],
            selected=owners({"레보티록신", "탄산칼슘", "황산철"}),
            mechanism=(
                "흡수(A): 탄산칼슘의 불용성 결합 또는 황산철과의 "
                "복합체 형성이 레보티록신 흡수를 감소시킬 수 있습니다."
            ),
        )

    food_text = " ".join(
        unicodedata.normalize("NFKC", str(food)) for food in foods
    )

    if "자몽" in food_text and "심바스타틴" in all_ingredients:
        add(
            "caution",
            "심바스타틴·자몽 · 식품 상호작용",
            (
                "자몽은 심바스타틴의 노출과 부작용 위험에 영향을 "
                "줄 수 있습니다. 모든 스타틴으로 확대하지 않습니다."
            ),
            "자몽이 포함된 식품을 알려 제품별 주의를 확인하세요.",
            SOURCES["grapefruit"],
            selected=owners({"심바스타틴"}),
            mechanism=(
                "대사(M): 자몽 성분이 장의 CYP3A4 작용을 억제하여 "
                "일부 약물의 혈중 노출을 증가시킬 수 있습니다."
            ),
        )

    if (
        "와파린" in all_ingredients
        and any(
            food in food_text
            for food in ("시금치", "브로콜리", "케일", "녹색채소")
        )
    ):
        add(
            "caution",
            "와파린·녹색채소 · 섭취량 일정하게",
            (
                "비타민 K가 많은 식품은 와파린 작용에 영향을 줄 수 "
                "있습니다. 녹색채소를 일괄 금지하지 않습니다."
            ),
            "평소와 비슷하게 섭취하고 큰 식단 변화 전 상담하세요.",
            SOURCES["warfarin"],
            selected=owners({"와파린"}),
        )

    if hypoglycemic and any(
        food in food_text
        for food in ("술", "음주", "맥주", "소주", "와인", "알코올")
    ):
        add(
            "caution",
            "혈당강하제·음주 · 저혈당 주의",
            (
                "인슐린·일부 혈당강하제를 사용하는 동안 음주, "
                "특히 음식 섭취가 부족한 상태의 음주는 "
                "저혈당 위험을 높일 수 있습니다."
            ),
            "음주 계획과 식사량을 당뇨 치료팀에 상담하세요.",
            SOURCES["hypo"],
            selected=hypoglycemic,
        )

    if foods and "만성콩팥병" in conditions:
        add(
            "unknown",
            "콩팥병 식단 · 개인 검사 확인 필요",
            (
                "재료만으로 칼륨·인·단백질·수분의 "
                "개인 허용량을 판단할 수 없습니다."
            ),
            "병기와 검사값을 바탕으로 영양사에게 확인하세요.",
            SOURCES["renal_diet"],
            "data",
        )

    if any(m.get("origin") == "demo" for m in products):
        add(
            "unknown",
            "체험용 가상 제품 · 실제 구매 판단에 사용 금지",
            (
                "이 제품명·성분은 기능 확인용 가상 예시이며 "
                "특정 판매 제품의 공식 정보가 아닙니다."
            ),
            "실제 포장에서 정확한 제품·함량을 확인하세요.",
            SOURCES["mfds"],
            "data",
        )

    add(
        "unknown",
        "점검 범위의 한계",
        (
            "등록·확인된 성분의 중복, 조회된 공식 DUR, 제한된 일반 "
            "주의를 표시합니다. 알레르기·용량·신장/간 기능·임신·"
            "전체 식품/보충제 상호작용을 완전히 평가하지 않습니다. "
            "표시되지 않은 위험이 있을 수 있습니다."
        ),
        "전체 약의 포장과 실제 복용 계획을 약사에게 제시하세요.",
        SOURCES["mfds"],
        "data",
        products,
    )

    order = {
        "contraindication": 0,
        "duplicate": 1,
        "caution": 2,
        "unknown": 3,
    }

    return sorted(findings, key=lambda finding: order[finding["level"]])


# ============================================================
# 시뮬레이션 데이터: 실제 판매 제품 아님
# ============================================================

def demo_med(
    identifier,
    name,
    ingredients,
    form="정제",
    kind="처방의약품",
):
    return {
        "id": identifier,
        "name": name,
        "kind": kind,
        "form": form,
        "ingredients": [
            {"name": name, "amount": amount, "code": ""}
            for name, amount in ingredients
        ],
        "confirmed": True,
        "origin": "demo",
        "ingredient_complete": True,
        "dur": [],
        "dur_complete": False,
        "elderly": [],
        "elderly_complete": False,
        "leaflet": {},
        "warnings": [],
    }


SIMULATIONS = [
    {
        "title": "당뇨·감기약 점검",
        "description": (
            "가상 복합감기약의 진통 성분 중복과 "
            "코막힘 성분 주의를 확인합니다."
        ),
        "conditions": ["당뇨병", "고혈압"],
        "older": True,
        "meds": [
            demo_med(
                "demo-insulin",
                "가상 기저 인슐린 예시",
                [("인슐린글라진", "100 단위/mL")],
                "주사제",
            ),
            demo_med(
                "demo-acet",
                "가상 단일 해열진통제 예시",
                [("아세트아미노펜", "500 mg")],
                kind="일반의약품",
            ),
        ],
        "candidate": demo_med(
            "demo-cold",
            "가상 3성분 감기약 예시",
            [
                ("아세트아미노펜", "300 mg"),
                ("슈도에페드린염산염", "15 mg"),
                ("클로르페니라민말레산염", "1.25 mg"),
            ],
            kind="일반의약품",
        ),
    },
    {
        "title": "관절통·신장·출혈 점검",
        "description": (
            "항응고제 복용 중 진통소염제 추가 시 "
            "확인할 사항을 보여주는 가상 예시입니다."
        ),
        "conditions": [
            "골관절염·관절통",
            "만성콩팥병",
            "위궤양·위장출혈 병력",
        ],
        "older": True,
        "meds": [
            demo_med(
                "demo-warfarin",
                "가상 항응고제 예시",
                [("와파린나트륨", "2 mg")],
            ),
        ],
        "candidate": demo_med(
            "demo-ibuprofen",
            "가상 진통소염제 예시",
            [("이부프로펜", "200 mg")],
            kind="일반의약품",
        ),
    },
    {
        "title": "인지저하·수면보조제 점검",
        "description": (
            "1세대 항히스타민 성분의 졸림·혼동과 "
            "배뇨 관련 주의를 확인하는 가상 예시입니다."
        ),
        "conditions": ["인지저하·치매", "녹내장·배뇨장애"],
        "older": True,
        "meds": [],
        "candidate": demo_med(
            "demo-diphenhydramine",
            "가상 수면보조 성분 예시",
            [("디펜히드라민염산염", "25 mg")],
            kind="일반의약품",
        ),
    },
]


# ============================================================
# 세션 상태
# ============================================================

def init_state():
    defaults = {
        "started": False,
        "demo_index": None,
        "candidate": None,
        "profiles": {
            "mine": {
                "name": "내 건강 프로필",
                "conditions": [],
                "older": False,
                "meds": [],
            },
            "diabetes": {
                "name": "당뇨병 프로필",
                "conditions": ["당뇨병"],
                "older": False,
                "meds": [],
            },
            "joints": {
                "name": "관절·혈압 프로필",
                "conditions": ["골관절염·관절통", "고혈압"],
                "older": False,
                "meds": [],
            },
        },
        "active_profile": "mine",
        "report": None,
        "search_results": None,
        "pending_med": None,
    }

    for key, value in defaults.items():
        if key not in st.session_state:
            st.session_state[key] = copy.deepcopy(value)

    if "snapshot_rows" not in st.session_state:
        st.session_state.snapshot_rows = copy.deepcopy(BUILTIN_OTC_ROWS)
        st.session_state.snapshot_source = "https://drug.hospitalk.net/item"
        st.session_state.snapshot_date = BUILTIN_OTC_ROWS[0].get("수집일", "미상")
        st.session_state.dataset_kind = "내장 교육자료 · 민간 재제공 · 약사 검수 전"


def context():
    index = st.session_state.demo_index

    if index is not None:
        scenario = SIMULATIONS[index]

        return {
            "name": scenario["title"],
            "conditions": scenario["conditions"],
            "older": scenario["older"],
            "meds": scenario["meds"],
            "foods": st.session_state.get("demo_foods", []),
            "food_exclusions": st.session_state.get(
                "demo_food_exclusions", []
            ),
        }, scenario["candidate"]

    return (
        st.session_state.profiles[st.session_state.active_profile],
        st.session_state.candidate,
    )


def invalidate_report():
    st.session_state.report = None
    st.session_state.pop("pdf_bytes", None)


def make_report():
    profile, candidate = context()
    foods = list(profile.get("foods", []))

    findings = analyze(
        profile["meds"],
        candidate,
        profile["conditions"],
        profile["older"],
        foods,
    )

    st.session_state.report = {
        "findings": findings,
        "created": now_kst(),
        "demo": st.session_state.demo_index is not None,
        "foods": foods,
        "food_exclusions": list(profile.get("food_exclusions", [])),
    }

    st.session_state.pop("pdf_bytes", None)


def launch_demo(index=0):
    st.session_state.demo_index = index
    st.session_state.started = True
    st.session_state.demo_foods = []
    st.session_state.demo_food_exclusions = []
    make_report()


def ingredient_label(med):
    labels = []

    for ingredient in med.get("ingredients", []):
        name = ingredient.get("name", "")
        amount = ingredient.get("amount", "")
        labels.append(name + (" " + amount if amount else ""))

    return " · ".join(labels) or "유효성분 미확인"


def brand():
    st.markdown(
        f"""
        <div class="brand">
            <div class="brand-icon">{CAPSULE}</div>
            <div>
                <div class="brand-title">
                    약결<span style="color:#0e8c7d">.</span>
                </div>
                <div class="brand-sub">MEDICATION COMPANION</div>
            </div>
        </div>
        """,
        unsafe_allow_html=True,
    )


def med_card(med, prefix="", compact=False):
    origin = {
        "official": "공식 조회",
        "manual": "직접 입력",
        "demo": "체험용 가상 제품",
    }.get(med.get("origin"), "미확인")

    ingredients = ingredient_label(med)

    if compact:
        ingredients = (
            f'유효성분 {len(med.get("ingredients", []))}개'
            " · 복용 목록에서 함량 확인"
        )

    st.markdown(
        f"""
        <div class="medline">
            <small>
                {h(prefix)} · {h(med.get("kind", "미확인"))}
                · {h(origin)}
            </small><br>
            <b>{h(med["name"])}</b><br>
            <small>{h(ingredients)}</small>
        </div>
        """,
        unsafe_allow_html=True,
    )


def add_medicine(med, target):
    if med.get("kind") != "일반의약품":
        st.warning("이 교육 앱은 일반의약품만 등록합니다. 전문의약품의 처방·조절은 다루지 않습니다.")
        return False
    if st.session_state.demo_index is not None:
        st.warning("실제 목록에 추가하려면 체험을 종료해 주세요.")
        return False

    profile = st.session_state.profiles[
        st.session_state.active_profile
    ]

    if target == "구매 예정":
        st.session_state.candidate = copy.deepcopy(med)
    else:
        if len(profile["meds"]) >= 25:
            st.warning("한 프로필은 25개까지 등록할 수 있습니다.")
            return False

        if any(m["id"] == med["id"] for m in profile["meds"]):
            st.warning("이미 등록된 제품입니다.")
            return False

        profile["meds"].append(copy.deepcopy(med))

    invalidate_report()
    return True


# ============================================================
# 설정·프로필·수기 입력
# ============================================================

@st.dialog("⚙️ 연결 설정 · 개인정보", width="large")
def settings_dialog():
    offline_data_panel()
    st.divider()
    st.markdown("**배포 파일 받기**")

    source_path = Path(__file__)
    requirements_path = source_path.with_name("requirements.txt")

    left, right = st.columns(2)

    if source_path.is_file():
        left.download_button(
            "📥 app.py",
            source_path.read_bytes(),
            file_name="app.py",
            mime="text/x-python",
            width="stretch",
        )

    if requirements_path.is_file():
        right.download_button(
            "📥 requirements.txt",
            requirements_path.read_bytes(),
            file_name="requirements.txt",
            mime="text/plain",
            width="stretch",
        )

    st.write(
        "**로그인 없이 사용합니다.** 질환과 약 목록은 서버의 "
        "접속 세션 메모리에 보관하며 데이터베이스에 저장하지 않습니다. "
        "같은 기기·열린 세션을 함께 쓰는 사람은 내용을 볼 수 있습니다."
    )

    st.caption(
        "이 버전에는 사용자별 접근 권한과 영구 저장 기능이 없습니다. "
        "사진은 앱 서버 메모리로 업로드됩니다. OCR에 동의한 경우에만 "
        "Google에 추가 전송합니다."
    )

    with st.form("key_settings"):
        st.text_input(
            "공공데이터포털 서비스 키",
            type="password",
            key="mfds_key",
        )
        st.text_input(
            "Google Cloud Vision API 키 · 사진 OCR 선택 기능",
            type="password",
            key="vision_key",
        )

        if st.form_submit_button(
            "설정 적용",
            type="primary",
            width="stretch",
        ):
            st.session_state.search_results = None
            st.session_state.pending_med = None
            st.rerun()

    st.markdown("**GitHub → Streamlit Community Cloud 배포**")

    st.code(
        "pip install -r requirements.txt\n"
        "streamlit run app.py",
        language="bash",
    )

    st.caption(
        "Python 3.14용 의존성 파일 동봉. GitHub 저장소에 두 파일을 올린 뒤 "
        "Streamlit 앱의 메인 파일을 app.py로 지정합니다."
    )

    st.code(
        'MFDS_SERVICE_KEY = "공공데이터포털_일반인증키"\n'
        '# 선택: GOOGLE_VISION_API_KEY = "클라우드_비전_API_키"',
        language="toml",
    )

    st.caption(
        "Streamlit 앱 Settings → Secrets에 입력합니다. "
        "키를 GitHub 저장소에 커밋하지 마세요. "
        "아래 세 API의 활용신청·승인은 각각 필요합니다."
    )

    st.markdown(
        "[의약품 제품 허가정보 08]"
        "(https://www.data.go.kr/data/15095677/openapi.do)"
        " · [DUR 품목정보 03]"
        "(https://www.data.go.kr/data/15059486/openapi.do)"
        " · [e약은요]"
        "(https://www.data.go.kr/data/15075057/openapi.do)"
    )

    st.caption(
        "식약처 조회에는 검색어·품목코드만 전송하며 "
        "프로필 질환은 전송하지 않습니다. "
        "Google OCR에는 동의한 사진이 전송됩니다."
    )

    if st.checkbox(
        "모든 프로필·약 목록·접속 세션 입력을 지우겠습니다",
        key="reset_agree",
    ):
        if st.button("세션 초기화", width="stretch"):
            for key in list(st.session_state):
                del st.session_state[key]
            st.rerun()


@st.dialog("👤 건강 프로필", width="large")
def profile_dialog():
    if st.session_state.demo_index is not None:
        st.info("체험을 종료한 뒤 실제 프로필을 수정할 수 있습니다.")
        return

    profile, _ = context()

    st.caption(
        "실명·생년월일·연락처를 수집하지 않습니다. "
        "프리셋의 질환과 연령을 실제 상태에 맞게 수정하세요."
    )

    with st.form("profile_form"):
        alias = st.text_input(
            "표시 이름",
            value=profile["name"],
            max_chars=30,
        )

        conditions = st.multiselect(
            "현재 확인된 질환",
            list(DISEASES),
            default=profile["conditions"],
            format_func=lambda disease: (
                f'{DISEASES[disease]["icon"]} {disease}'
            ),
        )

        older = st.checkbox(
            "65세 이상",
            value=profile["older"],
        )

        if st.form_submit_button(
            "프로필 저장",
            type="primary",
            width="stretch",
        ):
            profile.update(
                name=alias.strip() or "내 프로필",
                conditions=conditions,
                older=older,
            )
            invalidate_report()
            st.rerun()

    for disease in profile["conditions"]:
        data = DISEASES[disease]
        st.write(
            f'**{data["icon"]} {disease}** — {data["advice"]}'
        )
        evidence_url = safe_source_url(data.get("source", ""))
        if evidence_url:
            st.link_button("근거 자료 열기 · 외부 사이트", evidence_url)
        else:
            st.caption("근거 원문 URL 미확인 · 출처를 추가 확인하세요.")

    with st.expander("새 가족 프로필 만들기"):
        new_name = st.text_input(
            "새 프로필 표시 이름",
            max_chars=30,
        )

        if st.button(
            "빈 프로필 추가",
            disabled=len(st.session_state.profiles) >= 8,
        ):
            if not new_name.strip():
                st.warning("표시 이름을 입력해 주세요.")
            else:
                identifier = uuid.uuid4().hex[:10]

                st.session_state.profiles[identifier] = {
                    "name": new_name.strip(),
                    "conditions": [],
                    "older": False,
                    "meds": [],
                }

                st.session_state.active_profile = identifier
                st.session_state.pending_profile = identifier
                st.session_state.candidate = None
                invalidate_report()
                st.rerun()


@st.dialog("💊 복용 목록 · 직접 등록", width="large")
def medicine_dialog():
    profile, candidate = context()

    st.caption(
        "처방약·일반약·건강기능식품을 모두 알려주세요. "
        "인슐린은 종류·농도·혼합비·기기명을 그대로 기록합니다."
    )

    for index, med in enumerate(profile["meds"]):
        med_card(med, "현재 복용")

        if st.session_state.demo_index is None:
            if st.button("목록에서 삭제", key=f"remove_{index}"):
                profile["meds"].pop(index)
                invalidate_report()
                st.rerun()

    if candidate:
        med_card(candidate, "구매 예정")

        if st.session_state.demo_index is None:
            if st.button("구매 예정 선택 해제"):
                st.session_state.candidate = None
                invalidate_report()
                st.rerun()

    if st.session_state.demo_index is not None:
        st.info("체험 중에는 가상 예시 목록을 사용합니다.")
        return

    st.divider()
    st.write("**직접 입력 · 처방약/건강기능식품 포함**")

    st.caption(
        "유효성분을 한 줄에 하나씩 입력하세요. "
        "직접 입력 자료는 공식 DUR 조회가 수행되지 않습니다."
    )

    with st.form("manual_medicine"):
        name = st.text_input("정확한 제품명", max_chars=120)

        left, right = st.columns(2)

        kind = left.selectbox(
            "구분",
            ["일반의약품", "처방의약품", "건강기능식품"],
        )

        form = right.text_input(
            "제형·농도·혼합비",
            max_chars=100,
            placeholder="예: 정제 / U-100 주사",
        )

        raw = st.text_area(
            "유효성분 | 1정/1회 단위 함량",
            placeholder=(
                "아세트아미노펜 | 500 mg\n"
                "클로르페니라민말레산염 | 2 mg"
            ),
            height=90,
            max_chars=3000,
        )

        target = st.radio(
            "추가 위치",
            ["현재 복용", "구매 예정"],
            horizontal=True,
        )

        confirmed = st.checkbox(
            "입력한 제품명·성분은 라벨/처방전과 대조했습니다"
        )
        complete = st.checkbox(
            "전체 유효성분을 빠짐없이 입력했습니다"
        )

        submit = st.form_submit_button(
            "직접 등록",
            type="primary",
            width="stretch",
        )

    if submit:
        if not name.strip():
            st.warning("제품명을 입력해 주세요.")
            return

        ingredients = []

        for line in raw.splitlines():
            if not line.strip():
                continue

            parts = line.split("|", 1)

            ingredients.append({
                "name": parts[0].strip()[:160],
                "amount": (
                    parts[1].strip()[:100]
                    if len(parts) > 1 else ""
                ),
                "code": "",
            })

        if len(ingredients) > 30:
            st.error("유효성분은 30개 이하로 입력해 주세요.")
            return

        med = {
            "id": "manual:" + uuid.uuid4().hex,
            "name": name.strip(),
            "kind": kind,
            "form": form,
            "ingredients": ingredients,
            "confirmed": bool(confirmed),
            "ingredient_complete": bool(
                ingredients and complete and confirmed
            ),
            "origin": "manual",
            "source_url": "",
            "source_date": "",
            "fetched_at": now_kst(),
            "dur": [],
            "dur_complete": False,
            "elderly": [],
            "elderly_complete": False,
            "leaflet": {},
            "warnings": [
                "사용자 직접 입력. 공식 제품 식별·DUR 조회 미완료."
            ],
        }

        if add_medicine(med, target):
            st.rerun()


# ============================================================
# 제품 검색
# ============================================================

def run_search(query, barcode=False, page=1):
    st.session_state.open_search = False
    if not api_key() and not st.session_state.get("snapshot_rows"):
        st.warning(
            "검색용 자료가 없습니다. "
            "⚙ 설정에서 일반의약품 Excel·CSV를 업로드하거나 예시로 학습하세요."
        )
        return

    if st.session_state.demo_index is not None:
        st.warning("실제 제품 검색은 체험 종료 후 사용해 주세요.")
        return

    with st.spinner("일반의약품 학습 자료 검색 중…"):
        try:
            result = api_search(
                query,
                api_key(),
                barcode=barcode,
                page=page,
            )

            st.session_state.search_results = {
                **result,
                "query": query,
                "barcode": barcode,
            }

            st.session_state.pending_med = None
            st.session_state.open_search = True

        except ApiError as exc:
            st.session_state.search_results = None
            st.warning(str(exc))
            return

    st.rerun()


def close_search_dialog():
    st.session_state.open_search = False


@st.dialog("🔎 정확한 제품 선택", width="large", on_dismiss=close_search_dialog)
def search_dialog():
    result = st.session_state.search_results

    if result is None:
        st.info("검색어를 입력해 주세요.")
        return

    st.caption(
        f'‘{result["query"]}’ · 자료 후보 {result["total"]:,}개'
        " · 같은 이름이어도 제형·함량을 확인하세요."
    )

    items = result["items"]

    if not items:
        st.warning(
            "검색 결과가 없습니다. 이름 일부로 다시 검색하거나 "
            "포장을 확인해 직접 등록하세요. 자료 없음은 안전의 뜻이 아닙니다."
        )
        return

    def label(index):
        row = items[index]
        return (
            f'{row.get("ITEM_NAME", "이름 미확인")} | '
            f'{row.get("ENTP_NAME", "제조사 미확인")} | '
            f'{row.get("ITEM_SEQ", "")}'
        )

    selection = st.selectbox(
        "포장과 같은 제품을 선택",
        range(len(items)),
        format_func=label,
        key=f'pick_{result["query"]}_{result["page"]}',
    )

    row = items[selection]

    st.write(
        "**제형/성상:** "
        + (plain_text(row.get("CHART")) or "미제공")
    )
    st.write(
        "**분류:** "
        + (plain_text(row.get("ETC_OTC_CODE")) or "미확인")
        + " · **상태:** "
        + (plain_text(row.get("CANCEL_NAME")) or "미제공")
    )

    if st.button(
        "성분·자료 확인하기",
        type="primary",
        width="stretch",
    ):
        with st.spinner("품목 상세·DUR·노인주의 조회 중…"):
            try:
                detail = api_details(
                    str(row.get("ITEM_SEQ", "")),
                    api_key(),
                )

                st.session_state.pending_med = (
                    official_item_to_med(detail)
                )
            except ApiError as exc:
                st.warning(str(exc))

    med = st.session_state.pending_med

    if med and med["id"] == str(row.get("ITEM_SEQ", "")):
        med_card(med, "선택 제품 · 업로드 자료는 원본 대조 필요")

        st.caption(
            "원문 유효성분: "
            + (med.get("raw_ingredients") or "미제공")
        )

        if not med.get("ingredient_complete"):
            st.warning(
                "전체 성분을 완전하게 해석하지 못했습니다. "
                "공식 원문과 대조하거나 미확인 상태로 약사에게 확인하세요."
            )

        for message in med.get("warnings", []):
            st.caption(message)

        st.link_button(
            "의약품안전나라 제품 원문",
            med["source_url"],
            width="stretch",
        )

        st.caption(
            f'허가자료 변경일: {med.get("source_date") or "미제공"}'
            f' · 조회: {med.get("fetched_at", "")}'
        )

        with st.form("confirm_official"):
            target = st.radio(
                "추가 위치",
                ["구매 예정", "현재 복용"],
                horizontal=True,
            )

            checked = st.checkbox(
                "포장의 정확한 제품명·제형·함량과 위 제품이 일치합니다"
            )

            add = st.form_submit_button(
                "선택한 제품 등록",
                type="primary",
                width="stretch",
            )

        if add:
            status = str(med.get("status", ""))
            bad_status = status and status not in {
                "정상", "유효", "정상허가",
            }

            if not checked:
                st.warning("정확한 제품 일치 여부를 확인해 주세요.")

            elif target == "구매 예정" and bad_status:
                st.error(
                    "취하·취소 등 정상 여부를 확인해야 하는 품목입니다. "
                    "구매 전 약사와 확인해 주세요."
                )

            elif add_medicine(med, target):
                st.session_state.search_results = None
                st.session_state.pending_med = None
                st.session_state.open_search = False
                st.rerun()

    total_pages = math.ceil(result["total"] / 10)

    if total_pages > 1:
        left, right = st.columns(2)

        if left.button(
            "이전 후보",
            disabled=result["page"] <= 1,
            width="stretch",
        ):
            run_search(
                result["query"],
                result["barcode"],
                result["page"] - 1,
            )

        if right.button(
            "다음 후보",
            disabled=result["page"] >= total_pages,
            width="stretch",
        ):
            run_search(
                result["query"],
                result["barcode"],
                result["page"] + 1,
            )

        st.caption(f'{result["page"]}/{total_pages} 페이지')


# ============================================================
# 사진·바코드·OCR
# ============================================================

def prepare_image(upload):
    if upload.size > 8 * 1024 * 1024:
        raise ValueError("사진은 8 MB 이하로 선택해 주세요.")

    try:
        with Image.open(upload) as original:
            if original.width * original.height > 24_000_000:
                raise ValueError(
                    "2,400만 화소 이하 사진을 사용해 주세요."
                )

            image = ImageOps.exif_transpose(original).convert("RGB")
            image.thumbnail((2000, 2000))

            output = io.BytesIO()
            image.save(output, format="JPEG", quality=90)

            return image, output.getvalue()

    except (
        UnidentifiedImageError,
        OSError,
        Image.DecompressionBombError,
    ):
        raise ValueError(
            "사진 파일을 확인하지 못했습니다. JPG/PNG/WebP를 사용하세요."
        ) from None


def ocr_image(payload, key):
    if not key:
        raise ValueError(
            "Google Cloud Vision API 키를 먼저 설정하거나 "
            "약 이름을 직접 입력해 주세요."
        )

    body = {
        "requests": [{
            "image": {
                "content": base64.b64encode(payload).decode("ascii")
            },
            "features": [{"type": "DOCUMENT_TEXT_DETECTION"}],
            "imageContext": {"languageHints": ["ko", "en"]},
        }]
    }

    try:
        response = requests.post(
            "https://vision.googleapis.com/v1/images:annotate",
            headers={"X-Goog-Api-Key": key},
            json=body,
            timeout=(4, 25),
            allow_redirects=False,
        )

        if response.status_code != 200:
            raise ValueError(
                "OCR 요청을 완료하지 못했습니다. "
                "API 활성화·결제·키 제한을 확인해 주세요."
            )

        parsed = response.json()

        if (
            not isinstance(parsed, dict)
            or not isinstance(parsed.get("responses"), list)
            or not parsed["responses"]
            or not isinstance(parsed["responses"][0], dict)
        ):
            raise ValueError("OCR 응답 형식을 확인하지 못했습니다.")

        data = parsed["responses"][0]

        if data.get("error"):
            raise ValueError("OCR 서비스가 사진을 처리하지 못했습니다.")

        annotation = data.get("fullTextAnnotation") or {}

        if not isinstance(annotation, dict):
            raise ValueError("OCR 텍스트를 확인하지 못했습니다.")

        return str(annotation.get("text", ""))[:14000]

    except (
        requests.RequestException,
        json.JSONDecodeError,
        IndexError,
        TypeError,
    ):
        raise ValueError(
            "OCR 연결 또는 응답을 확인하지 못했습니다."
        ) from None


@st.dialog("📷 포장 사진 · 바코드", width="large")
def photo_dialog():
    st.caption(
        "제품명·유효성분·함량이 선명하게 보이도록 촬영하세요. "
        "OCR은 글자 추출을 돕는 기능이며 제품 확인을 대신하지 않습니다."
    )

    upload = st.file_uploader(
        "포장 사진",
        type=["jpg", "jpeg", "png", "webp"],
        key="package_upload",
    )

    with st.expander("카메라로 직접 촬영"):
        shot = st.camera_input("촬영", key="package_camera")

    chosen = shot or upload

    if chosen:
        try:
            image, payload = prepare_image(chosen)
            st.image(image, width=220)

            digest = hashlib.sha256(payload).hexdigest()

            if st.session_state.get("photo_digest") != digest:
                st.session_state.photo_digest = digest
                st.session_state.ocr_text = ""
                st.session_state.barcode_detected = ""

            left, right = st.columns(2)

            if left.button(
                "바코드 읽기",
                width="stretch",
            ):
                try:
                    import zxingcpp

                    codes = [
                        result.text
                        for result in zxingcpp.read_barcodes(image)
                        if result.text.isdigit()
                        and len(result.text) == 13
                    ]

                    st.session_state.barcode_detected = (
                        codes[0] if codes else ""
                    )

                    if not codes:
                        st.warning(
                            "13자리 코드를 찾지 못했습니다. "
                            "숫자를 직접 입력할 수 있습니다."
                        )

                except Exception:
                    st.warning(
                        "바코드 엔진을 실행하지 못했습니다. "
                        "코드를 직접 입력해 주세요."
                    )

            consent = st.checkbox(
                "사진을 Google Cloud Vision에 전송하는 데 동의합니다. "
                "이름·처방전 개인정보는 가려 주세요."
            )

            if right.button(
                "제품명·성분·함량 OCR",
                width="stretch",
                disabled=not consent,
            ):
                with st.spinner("글자 추출 중…"):
                    try:
                        st.session_state.ocr_text = ocr_image(
                            payload,
                            vision_key(),
                        )
                    except ValueError as exc:
                        st.warning(str(exc))

            st.text_area(
                "OCR 원문 · 오인식은 반드시 수정",
                key="ocr_text",
                height=120,
                max_chars=14000,
            )

            st.caption(
                "사진은 앱 서버 메모리에서 처리합니다. "
                "바코드 읽기에는 별도 외부 API를 사용하지 않습니다. "
                "OCR 텍스트는 자동으로 약 목록에 등록하지 않습니다."
            )

        except ValueError as exc:
            st.warning(str(exc))

    with st.form("photo_search"):
        mode = st.radio(
            "검색 방식",
            ["제품명", "13자리 바코드"],
            horizontal=True,
        )

        query = st.text_input(
            "확인·수정한 검색어",
            value=st.session_state.get("barcode_detected", ""),
            max_chars=80,
        )

        if st.form_submit_button(
            "공식 제품 검색",
            type="primary",
            width="stretch",
        ):
            st.session_state.open_search = True
            run_search(
                query,
                barcode=mode == "13자리 바코드",
            )


# ============================================================
# 결과 표시
# ============================================================

def finding_view(finding):
    icon, label, color = LEVELS.get(
        finding["level"],
        LEVELS["unknown"],
    )

    scope = SCOPE_LABELS.get(
        finding.get("scope"),
        "자료 점검",
    )

    mechanism = ""

    if finding.get("mechanism"):
        mechanism = (
            '<div class="detail"><b>기전</b> '
            + h(finding["mechanism"])
            + "</div>"
        )

    st.markdown(
        f"""
        <div class="resultrow" style="border-left:4px solid {color}">
            <div class="label" style="color:{color}">
                {h(icon)} {h(label)} · {h(scope)}
            </div>
            <div class="title">{h(finding["title"])}</div>
            <div class="detail">
                {h(plain_text(finding["detail"]))}
            </div>
            {mechanism}
            <div class="detail">
                <b>확인 방법</b> {h(finding["action"])}
            </div>
        </div>
        """,
        unsafe_allow_html=True,
    )

    source = safe_source_url(finding.get("source", ""))
    if source:
        st.link_button("근거 자료 열기 · 외부 사이트", source)
        st.caption("출처가 열리지 않으면 사이트에서 문서명을 검색하세요. 링크만으로 최신 개정 여부를 보장하지 않습니다.")
    else:
        st.caption("유효한 근거 원문 링크가 없습니다. 이 항목은 확인되지 않은 자료로 취급하세요.")


def refresh_official():
    profile, candidate = context()

    if st.session_state.demo_index is not None:
        st.info("체험 자료는 실제 API로 갱신하지 않습니다.")
        return

    if not api_key():
        st.warning("공식 API 키를 먼저 설정해 주세요.")
        return

    errors = []

    for med in profile["meds"] + ([candidate] if candidate else []):
        if med.get("origin") != "official":
            continue

        try:
            fresh = official_item_to_med(
                api_details(med["id"], api_key())
            )

            med.clear()
            med.update(fresh)

        except ApiError as exc:
            med["dur_complete"] = False
            med["elderly_complete"] = False
            med["warnings"] = [
                "재조회 미완료. 이전 조회 자료가 남아 있습니다.",
                str(exc),
            ]
            errors.append(med["name"])

    make_report()

    if errors:
        st.warning("일부 재조회 미완료: " + ", ".join(errors))


@st.dialog("🔎 점검 결과 · 공식 원문", width="large")
def results_dialog():
    profile, candidate = context()

    if not st.session_state.report:
        make_report()

    report = st.session_state.report

    st.caption(
        f'점검 시각: {report["created"]} · '
        + (
            "체험용 가상 제품"
            if report["demo"]
            else "현재 입력 목록 기준"
        )
    )

    st.warning(
        "추가 복용·중단·용량 변경을 이 결과만으로 결정하지 마세요. "
        "확인되지 않은 상호작용, 용량·시각·신장/간 기능·알레르기 "
        "위험이 남아 있습니다."
    )

    if candidate is None:
        st.info(
            "현재 복용 목록 내부만 점검했습니다. "
            "구매 예정 제품을 선택하면 함께 비교합니다."
        )

    if not report["demo"]:
        if st.button(
            "공식 자료 다시 조회 · 결과 갱신",
            width="stretch",
        ):
            with st.spinner("공식 등록 품목 재조회 중…"):
                refresh_official()
            st.rerun()

    for finding in st.session_state.report["findings"]:
        finding_view(finding)

    st.divider()
    st.write("**제품별 원자료 · 갱신 시점**")

    for med in profile["meds"] + ([candidate] if candidate else []):
        with st.expander(med["name"]):
            st.write("유효성분: " + ingredient_label(med))

            st.caption(
                f'제형/성상: {med.get("form") or "미확인"}'
                f' · 변경일: {med.get("source_date") or "미제공"}'
                f' · 조회: {med.get("fetched_at") or "미제공"}'
            )

            st.caption(
                "함량은 제품 원자료 단위입니다. "
                "하루 복용량이나 교환 가능한 투여량으로 계산하지 않습니다."
            )

            for warning in med.get("warnings", []):
                st.caption(warning)

            leaflet = med.get("leaflet", {})

            fields = [
                ("atpnWarnQesitm", "주의 경고"),
                ("atpnQesitm", "사용상 주의"),
                ("intrcQesitm", "약·음식 상호작용 원문"),
                ("seQesitm", "이상반응"),
            ]

            for key, title in fields:
                if leaflet.get(key):
                    st.write(f"**{title}**")
                    st.write(plain_text(leaflet[key]))

            st.caption(
                "e약은요 갱신일: "
                + str(leaflet.get("updateDe") or "미제공")
            )

            if med.get("official_warning_text"):
                st.write("**허가사항 주의 원문**")
                st.write(plain_text(med["official_warning_text"]))

            if med.get("source_url", "").startswith("https://"):
                st.link_button(
                    "식약처 제품 원문 열기",
                    med["source_url"],
                    width="stretch",
                )


# ============================================================
# 재료별 요리 및 약물-식품 주의
# ============================================================

RECIPES = [
    {
        "name": "두부·버섯 채소찜",
        "needs": {"두부", "버섯", "양배추"},
        "steps": [
            "두부와 채소를 먹기 편한 크기로 썹니다.",
            "냄비에 물을 조금 넣고 재료를 충분히 익힙니다.",
            "간은 먹기 전에 소량씩 조절합니다.",
        ],
        "note": (
            "당뇨병에서는 주식과 함께 식사 전체의 탄수화물 양을 "
            "확인하세요. 이 요리만으로 한 끼를 대체하도록 권하지 않습니다."
        ),
    },
    {
        "name": "닭고기·양배추 볶음",
        "needs": {"닭고기", "양배추", "당근"},
        "steps": [
            "생닭과 채소는 도마·집게를 구분해 준비합니다.",
            "닭고기 중심부가 충분히 익도록 조리합니다.",
            "채소를 넣어 익히고 양념은 소량으로 조절합니다.",
        ],
        "note": (
            "관절 증상을 치료하는 식단은 아닙니다. "
            "체중·활동 계획은 의료진과 상의하세요."
        ),
    },
    {
        "name": "달걀·버섯 부드러운 찜",
        "needs": {"달걀", "버섯", "당근"},
        "steps": [
            "달걀을 풀어 물과 잘게 썬 채소를 섞습니다.",
            "중심부까지 완전히 익도록 찝니다.",
            "사레가 잦다면 연하평가에 따른 음식 점도를 확인합니다.",
        ],
        "note": (
            "부드러운 질감의 조리 예시입니다. "
            "알레르기·단백질 처방량에 따라 바꾸세요."
        ),
    },
    {
        "name": "익힌 생선·브로콜리 한 접시",
        "needs": {"생선", "브로콜리", "당근"},
        "steps": [
            "생선의 잔가시를 충분히 제거합니다.",
            "생선과 채소를 각각 완전히 익힙니다.",
            "주식은 평소 처방식에 맞춰 별도로 곁들입니다.",
        ],
        "note": (
            "와파린 복용자는 녹색채소 섭취량을 "
            "갑자기 바꾸지 마세요."
        ),
    },
]

FOOD_CHOICES = [
    "두부", "버섯", "양배추", "당근", "닭고기", "달걀",
    "생선", "브로콜리", "시금치", "현미", "우유", "자몽", "술",
]


@st.dialog("🥗 재료로 찾는 식사 아이디어", width="large")
def food_dialog():
    profile, candidate = context()

    st.caption(
        "식단은 약을 대체하지 않습니다. 선택 재료의 조리 아이디어와 "
        "확인할 내용을 제공합니다."
    )

    profile_key = (
        "demo"
        if st.session_state.demo_index is not None
        else st.session_state.active_profile
    )

    foods = st.multiselect(
        "사용할 재료·함께 먹을 식품",
        FOOD_CHOICES,
        default=profile.get("foods", []),
        key=f"food_choices_{profile_key}",
    )

    exclusions = st.multiselect(
        "제외할 식품 · 알레르기·기호",
        ["콩", "달걀", "생선", "우유"],
        default=profile.get("food_exclusions", []),
        key=f"food_exclude_{profile_key}",
    )

    if st.button(
        "선택한 식품을 점검·상담 카드에 반영",
        width="stretch",
        type="primary",
    ):
        if st.session_state.demo_index is not None:
            st.session_state.demo_foods = list(foods)
            st.session_state.demo_food_exclusions = list(exclusions)
        else:
            profile["foods"] = list(foods)
            profile["food_exclusions"] = list(exclusions)

        make_report()
        st.success("점검 결과와 상담 카드에 반영했습니다.")

    st.caption(
        "알레르기 전수 점검 기능은 아닙니다. "
        "실제 원재료·교차오염 표시를 확인하세요."
    )

    findings = analyze(
        profile["meds"],
        candidate,
        profile["conditions"],
        profile["older"],
        foods,
    )

    for finding in findings:
        if (
            finding["level"] != "unknown"
            and any(
                word in finding["title"]
                for word in (
                    "자몽", "음주", "녹색", "비타민",
                    "식사", "칼륨", "식단",
                )
            )
        ):
            finding_view(finding)

    if "만성콩팥병" in profile["conditions"]:
        st.warning(
            "만성콩팥병 프로필: 병기·혈중 칼륨·인·단백질 "
            "처방량이 없어 자동 요리 추천을 보류합니다. "
            "선택 재료를 영양사에게 보여주세요."
        )
        st.markdown(
            f'[NIDDK 콩팥병 식사 안내]({SOURCES["renal_diet"]})'
        )
        return

    if "당뇨병" in profile["conditions"]:
        st.info(
            "탄수화물의 양·식사 시각·약물 계획을 함께 확인하세요. "
            "인슐린·저혈당 위험 약을 복용하면 결식과 급격한 "
            "식사량 변화에 주의합니다."
        )

    if set(profile["conditions"]) & {"고혈압", "심부전"}:
        st.caption(
            "나트륨과 수분의 구체적인 제한량은 "
            "개인 처방에 따라 확인하세요."
        )

    excluded = set(exclusions) & set(FOOD_CHOICES)

    if "콩" in exclusions:
        excluded.add("두부")

    available = set(foods) - excluded

    ranked = sorted(
        RECIPES,
        key=lambda recipe: len(recipe["needs"] & available),
        reverse=True,
    )

    count = 0

    for recipe in ranked:
        if (
            recipe["needs"] & excluded
            or not recipe["needs"] & available
        ):
            continue

        missing = recipe["needs"] - available

        with st.container(border=True):
            st.write(f'**🍽️ {recipe["name"]}**')
            st.caption(
                "재료: " + ", ".join(sorted(recipe["needs"]))
            )

            if missing:
                st.caption(
                    "추가 필요: " + ", ".join(sorted(missing))
                )

            for index, step in enumerate(recipe["steps"], 1):
                st.write(f"{index}. {step}")

            st.caption(
                recipe["note"]
                + " 정량 영양분석·치료식 검증을 거친 레시피는 아닙니다."
            )

        count += 1

        if count == 2:
            break

    if not count:
        st.info("조리 재료를 선택해 주세요.")


# ============================================================
# 카페인 계산 및 교육용 그래프
# ============================================================

def caffeine_total_from_rows(rows, medicine_mg=0.0):
    if not isinstance(rows, list) or len(rows) > 10:
        raise ValueError("입력은 10개 이내여야 합니다.")

    extra = float(medicine_mg)

    if not math.isfinite(extra) or not 0 <= extra <= 5000:
        raise ValueError("의약품·기타 카페인 입력을 확인하세요.")

    total = extra

    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("입력 형식을 확인하세요.")

        amount = float(row.get("1회 카페인(mg)", 0) or 0)
        count = float(row.get("오늘 횟수", 0) or 0)

        if not (
            math.isfinite(amount)
            and 0 <= amount <= 2000
            and math.isfinite(count)
            and 0 <= count <= 20
        ):
            raise ValueError("함량·횟수 범위를 확인하세요.")

        total += amount * count

    return total


def caffeine_decay_series(dose_mg, half_life_hours, hours=24):
    if not (
        math.isfinite(dose_mg)
        and 0 <= dose_mg <= 20000
    ):
        raise ValueError("초기값 범위를 확인하세요.")

    if not (
        math.isfinite(half_life_hours)
        and 0 < half_life_hours <= 100
    ):
        raise ValueError("반감기 범위를 확인하세요.")

    if not isinstance(hours, int) or not 1 <= hours <= 72:
        raise ValueError("표시 시간 범위를 확인하세요.")

    points = [index / 2 for index in range(hours * 2 + 1)]

    return {
        "경과 시간(h)": points,
        "교육 모델상 잔여량(mg)": [
            round(dose_mg * 0.5 ** (time / half_life_hours), 3)
            for time in points
        ],
    }


def caffeine_key(name):
    return re.sub(
        r"[\s_·.\-()]",
        "",
        unicodedata.normalize("NFKC", str(name)),
    ).casefold()


def caffeine_medication_notes(meds):
    rules = {
        "theophylline": ("테오필린", "MedlinePlus 테오필린"),
        "테오필린": ("테오필린", "MedlinePlus 테오필린"),
        "theophyllineanhydrous": (
            "테오필린", "MedlinePlus 테오필린"
        ),
        "무수테오필린": ("테오필린", "MedlinePlus 테오필린"),
        "aminophylline": ("아미노필린", "MedlinePlus 아미노필린"),
        "아미노필린": ("아미노필린", "MedlinePlus 아미노필린"),
        "aminophyllinehydrate": (
            "아미노필린", "MedlinePlus 아미노필린"
        ),
        "아미노필린수화물": (
            "아미노필린", "MedlinePlus 아미노필린"
        ),
        "pseudoephedrine": (
            "슈도에페드린", "MedlinePlus 슈도에페드린"
        ),
        "슈도에페드린": (
            "슈도에페드린", "MedlinePlus 슈도에페드린"
        ),
        "pseudoephedrinehydrochloride": (
            "슈도에페드린", "MedlinePlus 슈도에페드린"
        ),
        "슈도에페드린염산염": (
            "슈도에페드린", "MedlinePlus 슈도에페드린"
        ),
        "염산슈도에페드린": (
            "슈도에페드린", "MedlinePlus 슈도에페드린"
        ),
    }

    caffeine_aliases = {
        "caffeine", "caffeineanhydrous", "anhydrouscaffeine",
        "카페인", "무수카페인", "카페인무수물",
        "카페인수화물", "caffeinehydrate",
    }

    notes = []
    seen = set()

    for med in meds:
        if not med.get("confirmed", False):
            continue

        for ingredient in med.get("ingredients", []):
            name = ingredient.get("name", "")
            key = caffeine_key(name)
            match = rules.get(key)
            medname = med.get("name", "등록 약")

            if match and (medname, match[0]) not in seen:
                seen.add((medname, match[0]))
                drug, source = match

                notes.append({
                    "title": f"{medname} · {drug}",
                    "detail": (
                        "다량의 카페인이 이 약의 부작용을 심하게 할 수 "
                        "있다는 안내가 있습니다. 이 계산기로 병용 가능한 "
                        "양을 정하지 말고 제품 설명서와 약사 안내를 확인하세요."
                    ),
                    "source": CAFFEINE_SOURCES[source],
                })

            if (
                key in caffeine_aliases
                and (medname, "caffeine") not in seen
            ):
                seen.add((medname, "caffeine"))

                notes.append({
                    "title": f"{medname}에 카페인 성분 등록",
                    "detail": (
                        f'등록 함량: {ingredient.get("amount") or "미확인"}. '
                        "실제 복용 횟수를 확인한 뒤 ‘의약품·기타 하루 합계’에 "
                        "직접 반영하세요. 하루 복용량으로 자동 환산하지 않습니다."
                    ),
                    "source": CAFFEINE_SOURCES[
                        "FDA 성인 카페인 안내"
                    ],
                })

    return notes


def body_svg():
    return """
    <svg role="img"
         aria-label="교육용 인체: 뇌, 심장, 간, 소화관, 신장"
         viewBox="0 0 630 275"
         xmlns="http://www.w3.org/2000/svg"
         style="width:100%;max-height:270px">
      <rect width="630" height="275" rx="20" fill="#f0f7f7"/>
      <circle cx="309" cy="41" r="24"
              fill="#dcece9" stroke="#6d9e97"/>
      <path d="M287 70Q270 82 263 115L248 163Q245 179 258 178
               L282 129L280 193L273 253H294L309 204L325 253H346
               L337 191L336 128L358 174Q370 182 372 166
               L355 110Q349 78 332 70Z"
            fill="#dcece9" stroke="#6d9e97"/>
      <ellipse cx="309" cy="40" rx="14" ry="10" fill="#a995d3"/>
      <path d="M310 104Q300 90 294 101Q285 113 310 126
               Q332 110 322 101Q316 95 310 104"
            fill="#e9978e"/>
      <ellipse cx="321" cy="145" rx="18" ry="10" fill="#dfae68"/>
      <path d="M294 166H324Q337 177 300 177Q288 188 329 190"
            fill="none" stroke="#5bafa1" stroke-width="6"/>
      <ellipse cx="288" cy="146" rx="7" ry="11" fill="#a388b4"/>
      <g font-family="sans-serif" font-size="14" fill="#1b414f">
        <text x="27" y="50">뇌 · 졸림·각성·혼동</text>
        <path d="M225 45H290" stroke="#a995d3"/>
        <text x="395" y="111">심장 · 혈압·두근거림</text>
        <path d="M330 110H385" stroke="#e9978e"/>
        <text x="395" y="150">간 · 대사(M)</text>
        <path d="M342 145H385" stroke="#dfae68"/>
        <text x="27" y="143">신장 · 배설(E)</text>
        <path d="M170 140H280" stroke="#a388b4"/>
        <text x="27" y="185">소화관 · 흡수(A)</text>
        <path d="M190 180H288" stroke="#5bafa1"/>
        <text x="395" y="217">혈류 · 분포(D)</text>
        <text x="27" y="255" font-size="11" fill="#526b76">
          위치와 일반 경로를 보여주는 그림이며 손상·위험도를 뜻하지 않습니다.
        </text>
      </g>
    </svg>
    """


@st.dialog("☕ 카페인 · 인체·그래프", width="large")
def caffeine_dialog():
    profile, candidate = context()
    meds = profile["meds"] + ([candidate] if candidate else [])

    st.info(
        "최대 일일섭취권고량은 채워 마셔야 하는 목표나 "
        "약과 함께 섭취해도 되는 개인별 허용량이 아닙니다."
    )

    calc_tab, model_tab, sources_tab = st.tabs([
        "☕ 하루 총량",
        "🧍 인체·그래프",
        "📚 공식 근거",
    ])

    with calc_tab:
        basis = st.selectbox(
            "비교할 국내 기준",
            [
                "성인 일반 기준",
                "임산부 국내 기준",
                "어린이·청소년 국내 기준",
            ],
            key="caf_basis",
        )

        if basis == "어린이·청소년 국내 기준":
            weight = st.number_input(
                "체중(kg) · 이 세션에서만 사용",
                5.0,
                200.0,
                50.0,
                0.5,
                key="caf_weight",
            )

            limit = float(weight) * 2.5
            rule = "식약처: 체중 1kg당 2.5mg/일 이하"

            st.caption(
                "어린이·청소년에게 카페인 섭취를 권장하지 않습니다."
            )

        elif basis == "임산부 국내 기준":
            limit = 300.0
            rule = "식약처: 임산부 300mg/일 이하"

            st.caption(
                "담당 산부인과의 더 엄격한 지침이 있으면 따르세요."
            )

        else:
            limit = 400.0
            rule = "식약처: 성인 400mg/일 이하"

        st.caption(rule + " · 개인별 안전 보장 없음")

        if profile["older"]:
            st.warning(
                "65세 이상 프로필입니다. 일반 성인 기준을 개인 허용량으로 "
                "사용하지 마세요. 수면·두근거림·약물을 상담하세요."
            )

        st.caption(
            "아래 함량은 입력을 돕는 가상 예시입니다. "
            "실제 음료 라벨·제조사 함량으로 수정하세요."
        )

        defaults = [
            {
                "음료·식품": "예시 커피",
                "1회 카페인(mg)": 100.0,
                "오늘 횟수": 1.0,
            },
            {
                "음료·식품": "예시 차",
                "1회 카페인(mg)": 40.0,
                "오늘 횟수": 0.0,
            },
            {
                "음료·식품": "예시 에너지음료",
                "1회 카페인(mg)": 80.0,
                "오늘 횟수": 0.0,
            },
            {
                "음료·식품": "기타 식품",
                "1회 카페인(mg)": 0.0,
                "오늘 횟수": 0.0,
            },
        ]

        rows = st.data_editor(
            defaults,
            hide_index=True,
            num_rows="fixed",
            key="caf_food_rows",
            width="stretch",
            column_config={
                "음료·식품": st.column_config.TextColumn(
                    "음료·식품",
                    max_chars=40,
                ),
                "1회 카페인(mg)": st.column_config.NumberColumn(
                    "1회 mg",
                    min_value=0.0,
                    max_value=2000.0,
                    step=1.0,
                    required=True,
                ),
                "오늘 횟수": st.column_config.NumberColumn(
                    "오늘 횟수",
                    min_value=0.0,
                    max_value=20.0,
                    step=0.5,
                    required=True,
                ),
            },
        )

        medicine_mg = st.number_input(
            "의약품·기타에서 섭취한 카페인 하루 합계(mg)",
            min_value=0.0,
            max_value=5000.0,
            value=0.0,
            step=1.0,
            key="caf_other_mg",
        )

        try:
            total = caffeine_total_from_rows(
                rows,
                float(medicine_mg),
            )
        except (TypeError, ValueError, OverflowError):
            st.error("함량·횟수를 유한한 0 이상 숫자로 수정하세요.")
            return

        st.session_state.caffeine_last_total = total

        left, right = st.columns(2)
        left.metric("입력한 하루 합계", f"{total:,.0f} mg")
        right.metric("국내 기준과 비교", f"{total / limit * 100:,.0f}%")
        st.progress(min(total / limit, 1.0))

        if total > limit:
            st.warning(
                "입력한 총량이 선택한 최대 일일섭취권고량을 넘습니다. "
                "약의 복용량은 임의로 변경하지 말고 "
                "카페인 섭취와 증상을 상담하세요."
            )
        else:
            st.caption(
                "기준 이하라는 계산만으로 약과의 병용 가능 여부를 "
                "판단할 수 없습니다. 남은 허용량은 산출하지 않습니다."
            )

        notes = caffeine_medication_notes(meds)

        if notes:
            for note in notes:
                st.warning(note["title"] + "\n\n" + note["detail"])
                st.caption(
                    "해외 공공 의약품 일반 주의 · 국내 DUR 판정 아님"
                )
                st.markdown(
                    f'[해당 근거 확인]({note["source"]})'
                )
        else:
            st.caption(
                "이 도구가 다루는 일부 성분을 찾지 못했습니다. "
                "다른 약의 카페인 상호작용을 배제하지 않습니다."
            )

        if any(
            not med.get("ingredient_complete", False)
            for med in meds
        ):
            st.warning(
                "일부 약의 성분이 불완전합니다. "
                "카페인 포함 여부를 설명서에서 추가 확인하세요."
            )

        st.caption(
            "심한 두근거림·흉통·실신·경련 등 급성 증상이 있으면 "
            "계산을 계속하지 말고 응급의료기관에 도움을 요청하세요."
        )

    with model_tab:
        st.markdown(body_svg(), unsafe_allow_html=True)

        st.caption(
            "카페인은 소화관에서 흡수되어 전신에 분포하며 "
            "주로 간의 CYP1A2가 대사에 관여합니다. "
            "대사산물은 주로 소변으로 배출됩니다. "
            "근거는 공식 근거 탭의 NCBI 자료를 확인하세요."
        )

        initial = st.number_input(
            "모델 초기량(mg) · 실제 섭취량과 별도",
            0.0,
            2000.0,
            100.0,
            10.0,
            key="caf_model_initial",
        )

        half_life = st.slider(
            "교육용 가상 반감기(시간)",
            2.0,
            12.0,
            5.0,
            0.5,
            key="caf_half_life",
        )

        graph = caffeine_decay_series(
            float(initial),
            float(half_life),
        )

        st.line_chart(
            graph,
            x="경과 시간(h)",
            y="교육 모델상 잔여량(mg)",
            color="#138c80",
            height=230,
        )

        st.caption(
            "가정: 0시간에 한 번에 흡수되어 일정한 반감기로 감소. "
            "M(t) = M(0) × ½^(t/반감기)."
        )

        st.warning(
            "실제 혈중농도·체내 잔여량을 예측하지 않습니다. "
            "과거 누적 섭취·흡수 지연·약물 영향·개인 차이를 "
            "반영하지 않습니다. 복용 간격·다음 커피 시간·"
            "운전·수면 가능 여부를 결정하는 데 사용하지 마세요."
        )

        st.caption(
            "CDC 교육자료는 반감기를 약 5~6시간으로 설명합니다. "
            "슬라이더의 2~12시간 범위는 가정 비교용입니다."
        )

    with sources_tab:
        st.write(
            "**국내 최대 일일섭취권고량:** "
            "성인 400mg/일 이하, 임산부 300mg/일 이하, "
            "어린이·청소년 체중 1kg당 2.5mg/일 이하."
        )

        for title, url in CAFFEINE_SOURCES.items():
            st.markdown(f"- [{title}]({url})")

        st.caption(
            f"근거 검토일: {REVIEW_DATE}. "
            "일반 교육자료이며 국내 제품 허가사항을 대체하지 않습니다."
        )


# ============================================================
# 인체·약물 시뮬레이션
# ============================================================

def animated_adme(phase):
    # Schematic only: particle positions encode a lesson, never patient pharmacokinetics.
    import streamlit.components.v1 as components
    colors = {"복용 직후":"#d97706","흡수":"#0284c7","분포":"#be185d","대사":"#7c3aed","배설":"#15803d"}
    routes = {"복용 직후":"M190 78 L190 138 L210 185", "흡수":"M210 248 Q245 235 220 176", "분포":"M220 176 L185 105 L180 62 M220 176 L280 230", "대사":"M220 176 Q265 165 240 204", "배설":"M220 176 L165 211 L192 286 L192 320"}
    c=colors[phase]; path=routes[phase]
    active={"복용 직후":"gut","흡수":"gut","분포":"heart","대사":"liver","배설":"kidney"}[phase]
    def fill(part):return c if active==part else "#cbd5e1"
    markup=f'''<html><body style="margin:0;background:#f0f7f7;font-family:system-ui;color:#173744;border-radius:20px">
    <svg viewBox="0 0 560 360" role="img" aria-label="{phase} 단계 교육 모형" style="width:100%;max-height:370px">
    <style>@keyframes glow{{50%{{opacity:.45}}}} .active{{animation:glow 1.6s infinite}} @media(prefers-reduced-motion:reduce){{.active{{animation:none}}}}</style>
    <circle cx="190" cy="51" r="29" fill="#deeeeb" stroke="#629a96"/>
    <path d="M164 85 Q145 91 137 125 L111 225 Q115 239 128 226 L157 165 L157 251 L145 325 L169 325 L190 265 L210 325 L235 325 L223 251 L223 165 L252 226 Q267 237 270 224 L242 125 Q235 92 215 85 Z" fill="#deeeeb" stroke="#629a96"/>
    <path d="M190 78 L190 180" stroke="#93b4b0" fill="none" stroke-width="5"/>
    <path d="M177 244 Q231 230 199 221 Q166 213 214 206" fill="none" stroke="{fill('gut')}" stroke-width="12" class="{'active' if active=='gut' else ''}"/>
    <path d="M195 134 Q177 111 173 133 Q170 149 195 163 Q221 146 212 132 Q205 123 195 134" fill="{fill('heart')}"/>
    <ellipse cx="220" cy="188" rx="27" ry="14" fill="{fill('liver')}"/>
    <ellipse cx="160" cy="205" rx="10" ry="17" fill="{fill('kidney')}"/>
    <ellipse cx="217" cy="225" rx="10" ry="17" fill="{fill('kidney')}"/>
    <path d="{path}" fill="none" stroke="{c}" stroke-width="3" stroke-dasharray="6 5"/>
    <circle r="6" fill="{c}"><animateMotion dur="3s" repeatCount="indefinite" path="{path}"/></circle>
    <circle r="4" fill="{c}"><animateMotion dur="3s" begin="1s" repeatCount="indefinite" path="{path}"/></circle>
    <text x="310" y="75" font-size="24" font-weight="bold" fill="{c}">{phase}</text>
    <text x="310" y="117" font-size="16">● 약물 이동을 뜻하는 점</text>
    <text x="310" y="150" font-size="16">강조색 = 현재 학습 장기</text>
    <text x="310" y="193" font-size="16">입 → 소화관 → 혈액</text>
    <text x="310" y="223" font-size="16">→ 간·조직 → 배설 경로</text>
    <text x="20" y="349" font-size="12">교육용 개념도 · 실제 이동 속도·농도·장기 손상을 나타내지 않습니다.</text></svg></body></html>'''
    components.html(markup, height=390, scrolling=False)


def simulation_dialog():
    names = [scenario["title"] for scenario in SIMULATIONS]

    choice = st.selectbox(
        "체험 상황",
        range(len(names)),
        format_func=lambda index: names[index],
        index=st.session_state.demo_index or 0,
    )

    st.caption(SIMULATIONS[choice]["description"])

    if st.button(
        "이 상황으로 체험 시작",
        type="primary",
        width="stretch",
    ):
        launch_demo(choice)
        st.rerun()

    st.write("**인체·ADME 지도**")
    st.markdown("**🎯 색과 움직임으로 보는 흡수·분포·대사·배설**")
    phase = st.select_slider("모형 시간 단계", options=["복용 직후", "흡수", "분포", "대사", "배설"], key="education_adme_phase")
    animated_adme(phase)
    explanations={"복용 직후":"입과 위장관에 들어온 약: 제형에 따라 녹는 과정이 다릅니다.","흡수":"장 → 혈액: 모든 경구약이 같은 속도나 비율로 흡수되는 것은 아닙니다.","분포":"혈액 → 조직: 뇌·간·콩팥 등에 도달하는 양은 약마다 다릅니다.","대사":"주로 간에서 변화: 모든 약이 CYP로 대사되는 것은 아닙니다.","배설":"콩팥·담즙 등으로 제거: 신장 기능에 따른 판단은 의료진 영역입니다."}
    st.info(explanations[phase])
    import pandas as pd
    half = st.slider("가정한 반감기(시간) · 가상 모형", 1, 24, 6)
    st.line_chart(pd.DataFrame({"경과 시간(h)":list(range(49)), "가상 잔존 비율(%)":[100*2**(-t/half) for t in range(49)]}).set_index("경과 시간(h)"))
    st.caption("흡수 완료 시점부터 1차 소실만 가정한 수학 모형. 실제 제품·혈중 농도·효과·독성·다음 복용 시간을 예측하지 않습니다.")
    answer=st.radio("학습 확인: 다른 상품명 두 개에 같은 성분이 있으면?", ["선택하세요", "중복 가능성을 확인한다", "이름이 다르니 무조건 함께 먹는다"], key="edu_quiz")
    if answer=="중복 가능성을 확인한다": st.success("정답: 복합제까지 전체 유효성분을 확인하고, 실제 사용은 약사에게 상담하세요.")
    elif answer!="선택하세요": st.warning("상품명이 달라도 성분은 겹칠 수 있습니다.")


    st.caption(
        "일반적인 위치와 과정을 보여주는 교육 그림입니다. "
        "장기 손상·위험 확률·개인의 약물 농도는 계산하지 않습니다."
    )

    if st.session_state.report:
        mechanisms = [
            finding
            for finding in st.session_state.report["findings"]
            if finding.get("mechanism")
        ]

        if mechanisms:
            for finding in mechanisms:
                finding_view(finding)
        else:
            st.info(
                "현재 목록에서 출처로 확인한 개별 ADME 기전은 없습니다. "
                "성분 이름만으로 기전을 생성하지 않습니다."
            )

    st.caption(
        "고령자 항히스타민의 졸림 등은 약력학적 주의입니다. "
        "모든 주의를 CYP 효소 기전으로 설명하지 않습니다."
    )

    if st.button(
        "☕ 카페인 반감기 그래프도 보기",
        width="stretch",
    ):
        st.session_state.next_dialog = "caffeine"
        st.rerun()


# ============================================================
# 약사 상담 PDF
# ============================================================

def build_pdf(profile, candidate, report):
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.cidfonts import UnicodeCIDFont
    from reportlab.lib import colors
    from reportlab.lib.styles import ParagraphStyle
    from reportlab.lib.pagesizes import A4
    from reportlab.platypus import SimpleDocTemplate, Paragraph

    font = "HYSMyeongJo-Medium"

    if font not in pdfmetrics.getRegisteredFontNames():
        pdfmetrics.registerFont(UnicodeCIDFont(font))

    output = io.BytesIO()

    document = SimpleDocTemplate(
        output,
        pagesize=A4,
        topMargin=35,
        bottomMargin=35,
        leftMargin=38,
        rightMargin=38,
        title="약결 약사 상담 요약",
        author="약결",
    )

    body_style = ParagraphStyle(
        "body",
        fontName=font,
        fontSize=10,
        leading=16,
        wordWrap="CJK",
        textColor=colors.HexColor("#233c49"),
        spaceAfter=6,
    )

    title_style = ParagraphStyle(
        "title",
        parent=body_style,
        fontSize=17,
        leading=23,
        spaceAfter=12,
    )

    sub_style = ParagraphStyle(
        "sub",
        parent=body_style,
        fontSize=12,
        leading=18,
        textColor=colors.HexColor("#0d766e"),
        spaceBefore=10,
    )

    def paragraph(value, style=body_style):
        escaped = html.escape(str(value)).replace("\n", "<br/>")
        return Paragraph(escaped, style)

    story = [paragraph("약결 | 약사 상담 요약", title_style)]

    if report["demo"]:
        story.append(paragraph(
            "[체험용 가상 제품] 실제 환자·공식 품목 조회 결과가 아닙니다.",
            sub_style,
        ))

    story.append(paragraph(
        f'프로필: {profile["name"]} | 65세 이상: '
        + ("설정됨" if profile["older"] else "미설정")
    ))

    story.append(paragraph(
        "질환 설정: "
        + (", ".join(profile["conditions"]) or "없음/미입력")
    ))

    story.append(paragraph(
        "선택한 식품: "
        + (", ".join(report.get("foods", [])) or "미입력")
    ))

    story.append(paragraph(
        "제외할 식품: "
        + (", ".join(report.get("food_exclusions", [])) or "미입력")
    ))

    story.append(paragraph(
        "점검 시각: " + report["created"]
    ))

    story.append(paragraph(
        "복용 중단·추가·용량 변경은 이 문서만으로 결정하지 않습니다. "
        "약사·처방의가 실제 제품과 전체 복용 정보를 확인해야 합니다."
    ))

    groups = [
        ("현재 복용 목록", profile["meds"]),
        ("구매 예정", [candidate] if candidate else []),
    ]

    for title, meds in groups:
        story.append(paragraph(title, sub_style))

        if not meds:
            story.append(paragraph("미등록"))

        for med in meds:
            story.append(paragraph(
                f'{med["name"]} | {med.get("kind", "미확인")} '
                f'| {med.get("form", "")}'
            ))

            story.append(paragraph(ingredient_label(med)))

            story.append(paragraph(
                f'자료: {med.get("origin", "미확인")} '
                f'| 변경일: {med.get("source_date") or "미제공"} '
                f'| 조회: {med.get("fetched_at") or "미제공"}'
            ))

            if med.get("source_url"):
                story.append(paragraph(med["source_url"]))

    story.append(paragraph(
        "확인된 주의사항과 미확인 범위",
        sub_style,
    ))

    for index, finding in enumerate(report["findings"], 1):
        label = LEVELS.get(
            finding["level"],
            LEVELS["unknown"],
        )[1]

        scope = SCOPE_LABELS.get(
            finding.get("scope"),
            "자료 점검",
        )

        story.append(paragraph(
            f'{index}. [{label}] {finding["title"]}'
        ))

        story.append(paragraph("구분: " + scope))
        story.append(paragraph(plain_text(finding["detail"])))

        if finding.get("mechanism"):
            story.append(paragraph(
                "근거에 있는 기전: " + finding["mechanism"]
            ))

        story.append(paragraph(
            "확인 방법: " + finding["action"]
        ))

        story.append(paragraph(
            "출처: " + finding.get("source", "미제공")
        ))

    story.append(paragraph("상담할 질문", sub_style))

    story.append(paragraph(
        "1) 정확한 제형·함량의 제품인가요? "
        "2) 같은 성분이나 진통소염제 계열이 겹치나요? "
        "3) 식사·저혈당·카페인에서 무엇을 확인해야 하나요? "
        "4) 기존 처방과 복용 시각·용량을 어떻게 맞추나요?"
    ))

    story.append(paragraph(
        "개인별 용량·신장/간 기능·알레르기·복용 시각을 포함한 "
        "전수 평가가 아닙니다. 공식 DUR에 항목이 없어도 "
        "안전하다고 판정하지 않습니다."
    ))

    def footer(canvas, doc):
        canvas.setFont(font, 8)
        canvas.drawString(
            38,
            20,
            "약결 | 건강 정보가 포함된 상담 자료입니다.",
        )
        canvas.drawRightString(
            A4[0] - 38,
            20,
            str(doc.page),
        )

    document.build(
        story,
        onFirstPage=footer,
        onLaterPages=footer,
    )

    return output.getvalue()


@st.dialog("📄 약사 상담 카드", width="large")
def consultation_dialog():
    profile, candidate = context()

    if not st.session_state.report:
        make_report()

    report = st.session_state.report

    st.caption(
        "성분·주의사항·미확인 범위를 함께 전달합니다. "
        "다운로드 파일에 건강 정보가 포함됩니다."
    )

    st.write(f'**{profile["name"]}** · {report["created"]}')

    if report["demo"]:
        st.warning("체험용 가상 제품으로 만든 상담 예시입니다.")

    for med in profile["meds"]:
        med_card(med, "현재 복용")

    if candidate:
        med_card(candidate, "구매 예정")

    for finding in report["findings"]:
        label = LEVELS[finding["level"]][1]
        st.write(f'**[{label}] {finding["title"]}**')

    if st.button(
        "상담 PDF 만들기",
        type="primary",
        width="stretch",
    ):
        try:
            st.session_state.pdf_bytes = build_pdf(
                profile,
                candidate,
                report,
            )
        except Exception:
            st.error(
                "PDF를 만들지 못했습니다. "
                "화면의 상담 목록을 약사에게 보여주세요."
            )

    if st.session_state.get("pdf_bytes"):
        st.download_button(
            "📥 상담 요약 PDF 저장",
            st.session_state.pdf_bytes,
            file_name="yakgyeol_consultation.pdf",
            mime="application/pdf",
            width="stretch",
        )

        st.caption(
            "표준 한국어 CID 글꼴을 사용합니다. "
            "PDF 뷰어에 따라 글꼴이 대체될 수 있습니다."
        )


# ============================================================
# 성분 중복 탐지 성능 평가
# ============================================================

def evaluate_duplicate_csv(data):
    if len(data) > 1024 * 1024:
        raise ValueError("검증 CSV는 1 MB 이하로 업로드해 주세요.")

    try:
        reader = csv.DictReader(
            io.StringIO(data.decode("utf-8-sig"))
        )
    except UnicodeError:
        raise ValueError("UTF-8 CSV로 저장해 주세요.") from None

    required = {
        "case_id",
        "left_ingredients",
        "right_ingredients",
        "expected_duplicate",
        "source_url",
        "reviewed_on",
    }

    if not required.issubset(set(reader.fieldnames or [])):
        raise ValueError("필수 열이 없습니다. 템플릿을 사용해 주세요.")

    counts = {"TP": 0, "FP": 0, "FN": 0, "TN": 0}
    details = []
    identifiers = set()

    for row in reader:
        if len(details) >= 2000:
            raise ValueError("한 번에 2,000개 사례까지 평가합니다.")

        identifier = row.get("case_id", "").strip()
        left = row.get("left_ingredients", "")
        right = row.get("right_ingredients", "")
        label = row.get("expected_duplicate", "").strip()

        if (
            not identifier
            or identifier in identifiers
            or label not in {"0", "1"}
            or not left.strip()
            or not right.strip()
        ):
            raise ValueError(
                "ID는 유일해야 하며 성분과 0/1 정답이 필요합니다."
            )

        if (
            not row.get("source_url", "").startswith("https://")
            or not re.fullmatch(
                r"\d{4}-\d{2}-\d{2}",
                row.get("reviewed_on", ""),
            )
        ):
            raise ValueError(
                "각 사례에 근거 URL과 검토일(YYYY-MM-DD)이 필요합니다."
            )

        identifiers.add(identifier)

        a = {
            normalize_ingredient(value.strip())
            for value in left.split("|")
            if value.strip()
        }

        b = {
            normalize_ingredient(value.strip())
            for value in right.split("|")
            if value.strip()
        }

        predicted = bool(a & b)
        expected = label == "1"

        if predicted and expected:
            result = "TP"
        elif predicted:
            result = "FP"
        elif expected:
            result = "FN"
        else:
            result = "TN"

        counts[result] += 1

        details.append({
            "case_id": identifier,
            "정답": int(expected),
            "예측": int(predicted),
            "결과": result,
        })

    if not details:
        raise ValueError("평가할 사례가 없습니다.")

    tp = counts["TP"]
    fp = counts["FP"]
    fn = counts["FN"]

    precision = tp / (tp + fp) if tp + fp else None
    recall = tp / (tp + fn) if tp + fn else None

    f1 = (
        2 * tp / (2 * tp + fp + fn)
        if 2 * tp + fp + fn else None
    )

    return {
        **counts,
        "precision": precision,
        "recall": recall,
        "f1": f1,
        "rows": details,
    }


@st.dialog("🔬 근거 · 성분 중복 탐지 평가", width="large")
def evidence_dialog():
    st.write("**공식 제품 성분표와 전문가 정답으로 검증**")

    st.caption(
        f"앱 {APP_VERSION} · 근거·API 명세 검토일: {REVIEW_DATE}. "
        "공식 데이터 갱신일·임상 검증일과는 다릅니다."
    )

    st.write(
        "아래 평가는 입력된 성분 목록의 제품 쌍 단위 중복 탐지만 "
        "측정합니다. 검색 정확도·OCR·DUR 누락·임상 결과의 정확도를 "
        "대신하지 않습니다. 공식 원문을 바탕으로 독립 검토한 "
        "정답 세트가 필요합니다."
    )

    template = (
        "case_id,left_ingredients,right_ingredients,"
        "expected_duplicate,source_url,reviewed_on\n"
    )

    st.download_button(
        "검증 CSV 빈 템플릿",
        template.encode("utf-8-sig"),
        file_name="duplicate_validation_template.csv",
        mime="text/csv",
        width="stretch",
    )

    st.caption(
        "성분 구분자는 |, 정답은 중복 1/비중복 0입니다. "
        "정답의 임상적 타당성을 앱이 자동 인증하지 않습니다."
    )

    uploaded = st.file_uploader(
        "독립 검증 CSV",
        type=["csv"],
        key="evaluation_csv",
    )

    if uploaded:
        try:
            result = evaluate_duplicate_csv(uploaded.getvalue())
            columns = st.columns(3)

            for column, key, title in zip(
                columns,
                ["precision", "recall", "f1"],
                ["정밀도", "재현율", "F1"],
            ):
                value = result[key]
                column.metric(
                    title,
                    f"{value:.3f}" if value is not None else "정의 불가",
                )

            st.caption(
                f'TP {result["TP"]} · FP {result["FP"]} · '
                f'FN {result["FN"]} · TN {result["TN"]}'
            )

            st.dataframe(
                result["rows"],
                hide_index=True,
                width="stretch",
            )

        except (ValueError, csv.Error) as exc:
            st.error(str(exc))

    st.divider()

    st.write(
        "한국 허가정보 08은 품목·유효성분 식별에, DUR 03은 정확한 "
        "품목 쌍의 공식 금기와 노인주의에 사용합니다. "
        "e약은요는 일부 일반약의 쉬운 원문을 보완합니다."
    )

    st.caption(
        "건강기능식품 성분 DB·모든 질환별 금기·총 복용량·"
        "신장/간 기능별 용량을 전수 점검하지 않습니다. "
        "생성형 AI로 금기·기전을 생성하지 않습니다."
    )

    st.markdown(
        "[식약처 허가정보]"
        "(https://www.data.go.kr/data/15095677/openapi.do)"
        " · [DUR]"
        "(https://www.data.go.kr/data/15059486/openapi.do)"
        " · [e약은요]"
        "(https://www.data.go.kr/data/15075057/openapi.do)"
    )


# ============================================================
# 시작 화면 및 본 화면
# ============================================================

def landing():
    brand()
    st.caption("일반의약품 교육용 · 질환별 주의 학습 · 처방 판단·안전 보증·진단 도구 아님")

    st.markdown(
        """
        <div class="hero">
            <div class="eyebrow">MY MEDICATION, CONNECTED</div>
            <h1>우리 집 약상자,<br>성분부터 배워보세요.</h1>
            <p>
                약 이름 일부로 내장 자료를 검색해 보세요.<br>
                복용 중인 약과 구매할 약을 함께 살펴보고,<br>
                나의 질환·식사·카페인까지 확인하세요.
            </p>
            <div class="hero-tag">
                로그인 없이 · 큰 버튼으로 · 근거와 함께
            </div>
        </div>
        <div class="intro-features">
            <div class="intro-feature">
                <span>💊</span>
                <b>성분 중복·주의</b>
                <small>제품명 대신 성분으로</small>
            </div>
            <div class="intro-feature">
                <span>🧍</span>
                <b>10개 질환 맞춤</b>
                <small>당뇨·혈압·인지건강</small>
            </div>
            <div class="intro-feature">
                <span>☕</span>
                <b>식사·카페인</b>
                <small>인체·그래프 체험</small>
            </div>
        </div>
        """,
        unsafe_allow_html=True,
    )

    if st.button(
        "시작하기  →",
        type="primary",
        width="stretch",
    ):
        st.session_state.started = True
        st.rerun()

    if st.button(
        "▶  예시로 먼저 체험하기",
        width="stretch",
    ):
        launch_demo(0)
        st.rerun()

    st.markdown(
        """
        <div class="footer-note">
            추가 복용을 결정하기 전 확인을 돕는 도구입니다.<br>
            복용 중단·용량 변경은 약사·의사와 상의하세요.
        </div>
        """,
        unsafe_allow_html=True,
    )


def main():
    st.set_page_config(
        page_title="약결 | 약·질환·카페인 확인",
        page_icon="💊",
        layout="centered",
        initial_sidebar_state="expanded",
    )

    st.markdown(CSS, unsafe_allow_html=True)
    st.markdown("""<style>
    .stButton button,.stFormSubmitButton button,.stDownloadButton button,.stLinkButton a,
    button[kind="primary"],button[kind="secondary"]{background:#fff!important;color:#111!important;border:1px solid #82949b!important;}
    .stButton button *,.stFormSubmitButton button *,.stDownloadButton button *{color:#111!important;}
    .stButton button:hover,.stFormSubmitButton button:hover{background:#edf4f4!important;border-color:#15686b!important;}
    </style>""", unsafe_allow_html=True)
    init_state()
    with st.sidebar:
        st.markdown("## 💊 약결 메뉴")
        page = st.radio("화면 선택", ["💊 약 관리", "🎓 교육용"], key="app_navigation")
        st.divider()
    if page == "🎓 교육용":
        st.header("🎓 일반의약품 교육실")
        st.info("학습목표: ① 흡수·분포·대사·배설 구분 ② 성분 중복 확인 ③ 미확인과 안전 구별")
        st.caption("실제 제품별 농도·복용량·복용 간격을 계산하지 않는 개념 학습 화면입니다.")
        simulation_dialog()
    else:
        management_section()


def management_section():
    st.caption("🎓 일반의약품 교육용 · 506품목 내장 | 학습목표: 성분 중복 찾기 · 질환별 주의 읽기 · 미확인과 안전 구별하기")

    if not st.session_state.started:
        landing()
        return

    profile, candidate = context()
    demo = st.session_state.demo_index is not None

    header1, header2, header3 = st.columns(
        [6, 1.1, 1.1],
        vertical_alignment="center",
    )

    with header1:
        brand()
    st.caption("일반의약품 교육용 · 질환별 주의 학습 · 처방 판단·안전 보증·진단 도구 아님")

    if header2.button("홈", width="stretch"):
        st.session_state.started = False
        st.rerun()

    if header3.button(
        "⚙",
        help="API 연결·배포 방법·개인정보",
        width="stretch",
    ):
        settings_dialog()

    if demo:
        left, right = st.columns(
            [5, 2],
            vertical_alignment="center",
        )

        left.caption("▶ 체험 중 · 가상 제품, 실제 복용 지침 아님")

        if right.button("체험 종료", width="stretch"):
            st.session_state.demo_index = None
            invalidate_report()
            st.rerun()
    else:
        st.caption("구매 전, 약 이름보다 성분을 먼저 확인해요.")

    left, right = st.columns(
        [4, 1.35],
        vertical_alignment="bottom",
    )

    with left:
        keys = list(st.session_state.profiles)
        names = {
            key: st.session_state.profiles[key]["name"]
            for key in keys
        }

        if "pending_profile" in st.session_state:
            st.session_state.profile_select = (
                st.session_state.pop("pending_profile")
            )

        if demo:
            st.selectbox(
                "체험 프로필",
                ["체험 · " + profile["name"]],
                disabled=True,
                label_visibility="collapsed",
                key="demo_profile_select",
            )
            selection = st.session_state.active_profile

        else:
            selection = st.selectbox(
                "건강 프로필",
                keys,
                index=keys.index(st.session_state.active_profile),
                format_func=names.get,
                label_visibility="collapsed",
                key="profile_select",
            )

        if (
            selection != st.session_state.active_profile
            and not demo
        ):
            st.session_state.active_profile = selection
            st.session_state.candidate = None
            st.session_state.search_results = None
            invalidate_report()
            st.rerun()

    if right.button("👤 설정", width="stretch"):
        profile_dialog()

    with st.sidebar:
        st.markdown("### 💊 선택한 복용 약")
        st.caption("추가한 순서대로 유지됩니다. 모바일에서는 왼쪽 위 펼치기로 볼 수 있습니다.")
        if not profile["meds"]:
            st.info("검색 결과에서 ‘복용 중’으로 추가하세요.")
        for idx, med in enumerate(profile["meds"]):
            st.write(f"{idx+1}. {med['name']}")
            if not demo and st.button("목록에서 삭제", key="rail_remove_"+str(med["id"])):
                profile["meds"].pop(idx)
                invalidate_report()
                st.rerun()
        if candidate:
            st.markdown("#### 구매 예정")
            st.write(candidate["name"])
        st.caption("목록 추가는 실제 복용을 지시하거나 복용 완료를 의미하지 않습니다.")

    condition_html = " ".join(
        (
            '<span class="pill">'
            f'{h(DISEASES[disease]["icon"])} {h(disease)}'
            "</span>"
        )
        for disease in profile["conditions"][:2]
    )

    if len(profile["conditions"]) > 2:
        condition_html += (
            '<span class="pill">'
            f'외 {len(profile["conditions"]) - 2}개'
            "</span>"
        )

    age_html = (
        '<span class="pill">65세 이상</span>'
        if profile["older"] else ""
    )

    st.markdown(
        '<div class="context">'
        + age_html
        + (
            condition_html
            or "질환이 있으면 프로필에서 선택해 주세요."
        )
        + "</div>",
        unsafe_allow_html=True,
    )

    with st.form("name_search", border=False):
        search1, search2 = st.columns(
            [4, 1.15],
            vertical_alignment="bottom",
        )

        query = search1.text_input(
            "약 이름 일부로 검색",
            placeholder="타이레놀, 하벤…",
            label_visibility="collapsed",
            key="search_input",
            max_chars=80,
        )

        submit = search2.form_submit_button(
            "🔎 검색",
            width="stretch",
        )

    if submit:
        st.session_state.open_search = True
        run_search(query)

    if (
        st.session_state.get("open_search", False)
        and st.session_state.search_results
    ):
        search_dialog()

    action1, action2 = st.columns(2)

    if action1.button(
        f'💊 복용 목록 {len(profile["meds"])}개',
        width="stretch",
    ):
        medicine_dialog()

    if action2.button(
        "📷 사진·바코드",
        width="stretch",
    ):
        photo_dialog()

    if candidate:
        med_card(candidate, "구매 예정", compact=True)
    else:
        st.markdown(
            '<div class="empty">'
            "＋ 검색 후 <b>구매 예정 약</b>을 선택해 주세요"
            "</div>",
            unsafe_allow_html=True,
        )

    if st.button(
        "내 약과 함께 점검하기",
        type="primary",
        width="stretch",
    ):
        make_report()

    report = st.session_state.report

    if report:
        counts = {
            level: sum(
                finding["level"] == level
                for finding in report["findings"]
            )
            for level in LEVELS
        }

        metric1, metric2, metric3 = st.columns(3)

        metric1.metric(
            "⛔ 금기·중복 검출",
            counts["contraindication"] + counts["duplicate"],
        )
        metric2.metric("! 확인 필요", counts["caution"])
        metric3.metric("? 미확인", counts["unknown"])

        if st.button(
            "근거·확인 방법 보기",
            width="stretch",
        ):
            results_dialog()

    else:
        status = (
            "키 설정됨 · 실제 연결은 조회 시 확인"
            if api_key()
            else "미연결 · 설정에서 키 입력"
        )

        st.caption(
            f"내장 일반의약품 {len(st.session_state.get('snapshot_rows', [])):,}품목 · 키 없이 검색 가능 · 교육용"
        )

    feature1, feature2, feature3 = st.columns(3)

    if feature1.button("🥗 식단", width="stretch"):
        food_dialog()

    if feature2.button("☕ 카페인", width="stretch"):
        caffeine_dialog()

    if feature3.button("📄 상담", width="stretch"):
        consultation_dialog()

    bottom1, bottom2 = st.columns(2)

    bottom1.caption("🎓 상세 학습과 퀴즈는 왼쪽 메뉴 → 교육용")

    if bottom2.button(
        "🔬 근거·평가",
        width="stretch",
    ):
        evidence_dialog()

    st.divider()
    st.subheader("🧍 인체로 보는 약의 이동")
    st.caption("아래 단계를 바꾸면 장기 색과 약물을 나타내는 이동 점이 바뀝니다.")
    home_phase = st.select_slider(
        "체내 이동 단계",
        options=["복용 직후", "흡수", "분포", "대사", "배설"],
        key="management_adme_phase",
    )
    animated_adme(home_phase)
    descriptions = {
        "복용 직후": "입 → 소화관: 경구약이 들어와 녹는 과정을 개념적으로 보여줍니다.",
        "흡수": "소화관 → 혈액: 약 성분이 혈액으로 흡수되는 과정을 보여줍니다.",
        "분포": "혈액 → 조직: 혈액을 따라 여러 조직으로 이동하는 과정입니다.",
        "대사": "간 등에서 성분이 변화하는 과정입니다. 약마다 대사 경로는 다릅니다.",
        "배설": "콩팥·담즙 등의 경로로 제거됩니다. 모든 약이 같은 경로를 따르지는 않습니다.",
    }
    st.info(descriptions[home_phase])
    st.caption("경구약의 일반적 과정을 단순화한 교육 모형입니다. 실제 약의 이동 순서·속도·농도·효과를 예측하지 않습니다.")

    next_dialog = st.session_state.pop("next_dialog", None)

    if next_dialog == "caffeine":
        caffeine_dialog()

    st.markdown(
        '<div class="footer-note main-footer">'
        "자료 없음 ≠ 안전 · 추가 복용 전 약사와 확인하세요."
        "</div>",
        unsafe_allow_html=True,
    )


if __name__ == "__main__":
    main()