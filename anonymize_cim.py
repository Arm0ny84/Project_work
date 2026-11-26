"""Stream a CIM RDF/XML export and replace identifying values."""

import argparse
import base64
from collections import Counter, defaultdict
from datetime import date, datetime
import functools
import hashlib
import hmac
import io
import ipaddress
from itertools import zip_longest
import json
import os
from pathlib import Path
import re
import secrets
import sqlite3
import sys
from tempfile import TemporaryDirectory
import uuid
import wave
from zipfile import BadZipFile, ZIP_DEFLATED, ZipFile, ZipInfo

from lxml import etree
from PIL import Image
from urllib.parse import urlsplit
from xml.sax.saxutils import escape, quoteattr


RDF = '{http://www.w3.org/1999/02/22-rdf-syntax-ns#}'
RDF_IDS = {RDF + 'about', RDF + 'ID', RDF + 'nodeID'}
RDF_VALUE = RDF + 'resource'
XML_BASE = '{http://www.w3.org/XML/1998/namespace}base'
XML_SPACE = '{http://www.w3.org/XML/1998/namespace}space'
TECHNICAL_ATTRIBUTES = {RDF + 'datatype', RDF + 'parseType',
                        '{http://www.w3.org/XML/1998/namespace}lang', XML_SPACE}
# The value is a CIM classification code, even though the field name ends in "Name".
CLASSIFIER_FIELDS = {'PSRType.className'}
GUID = re.compile(r'[a-f0-9]{8}(?:-[a-f0-9]{4}){3}-[a-f0-9]{12}', re.I)
DECIMAL = re.compile(r'[0-9]+')
SCALAR = re.compile(
    r'(?i)(?:true|false|[+-]?(?:\d+(?:[.,]\d*)?|[.,]\d+)(?:e[+-]?\d+)?)'
)
PLACEHOLDER = re.compile(
    r'\{[0-9]+(?:,-?[0-9]+)?(?::[A-Za-z0-9.#%+ /:,\-]+)?\}|%[sdif]|\$\{[A-Za-z0-9_.]+\}'
)

# First name, surname, patronymic, e-mail spelling and street spelling.
PEOPLE = (
    ('Алёна', 'Алёнина', 'Алёновна', 'alena', 'Алёнина'),
    ('Вера', 'Верина', 'Веровна', 'vera', 'Верина'),
    ('Дарья', 'Дарьина', 'Дарьевна', 'darya', 'Дарьина'),
    ('Елена', 'Еленина', 'Еленовна', 'elena', 'Еленина'),
    ('Ирина', 'Иринина', 'Ириновна', 'irina', 'Иринина'),
    ('Лада', 'Ладина', 'Ладовна', 'lada', 'Ладина'),
    ('Антон', 'Антонов', 'Антонович', 'anton', 'Антонова'),
    ('Арсений', 'Арсеньев', 'Арсеньевич', 'arseniy', 'Арсеньева'),
    ('Борис', 'Борисов', 'Борисович', 'boris', 'Борисова'),
    ('Вадим', 'Вадимов', 'Вадимович', 'vadim', 'Вадимова'),
    ('Илья', 'Ильин', 'Ильич', 'ilya', 'Ильина'),
    ('Мирон', 'Миронов', 'Миронович', 'miron', 'Миронова'),
    ('Олег', 'Олегов', 'Олегович', 'oleg', 'Олегова'),
    ('Роман', 'Романов', 'Романович', 'roman', 'Романова'),
    ('Тимур', 'Тимуров', 'Тимурович', 'timur', 'Тимурова'),
    ('Яков', 'Яковлев', 'Яковлевич', 'yakov', 'Яковлева'),
)
PRODUCE = (
    ('абрикос', 'Абрикосовый'), ('ананас', 'Ананасовый'),
    ('апельсин', 'Апельсиновый'), ('баклажан', 'Баклажановый'),
    ('виноград', 'Виноградный'), ('гранат', 'Гранатовый'),
    ('груша', 'Грушевый'), ('кабачок', 'Кабачковый'),
    ('капуста', 'Капустный'), ('лимон', 'Лимонный'),
    ('морковь', 'Морковный'), ('персик', 'Персиковый'),
    ('редис', 'Редисовый'), ('слива', 'Сливовый'),
    ('тыква', 'Тыквенный'), ('яблоко', 'Яблочный'),
)

CLASS_LABELS = {
    'ACLineSegment': 'ЛЭП', 'Line': 'ЛЭП', 'ACLineSeriesSection': 'Участок ЛЭП',
    'PowerTransformer': 'Т', 'PowerTransformerEnd': 'Обмотка',
    'Substation': 'ПС', 'SubstationSLD': 'Схема ПС', 'Pole': 'Опора',
    'Bay': 'Присоединение', 'VoltageLevel': 'РУ', 'Breaker': 'Выключатель',
    'BusbarSection': 'Секция шин', 'Disconnector': 'Разъединитель',
    'ConnectivityNode': 'Узел', 'Terminal': 'Терминал', 'Meter': 'Счётчик',
    'DistributionSubstation': 'ТП', 'DistributionPoint': 'РП',
    'ServiceLocation': 'Точка обслуживания', 'Organisation': 'Организация',
    'Customer': 'Абонент', 'ModelingAuthoritySet': 'Модель',
}
PERSON_CLASSES = {'Person', 'Employee', 'Individual', 'NaturalPerson', 'StaffMember'}
PERSON_NAME_FIELDS = {
    'firstname', 'givenname', 'lastname', 'surname', 'familyname', 'middlename', 'patronymic',
}
PERSON_LABELS = {'fullname', 'fio', 'inchargefullname', 'contactname', 'ownername'}
PERSON_NAME = re.compile(r'[А-ЯЁ][а-яё-]+\s+[А-ЯЁ][а-яё-]+(?:\s+[А-ЯЁ][а-яё-]*(?:ич|ны|на))?')
TECHNICAL_TEXT = {
    'Asset.type', 'BasicIntervalSchedule.points', 'CalendarDay.date',
    'CurrentTransformer.accuracyClass', 'CurrentTransformer.ctClass',
    'CurrentTransformer.ioptsat', 'CurrentTransformer.it2p2', 'CurrentTransformer.it2pl',
    'CurrentTransformer.pbranch', 'Curve.points', 'DocumentType.contentType',
    'DocumentType.fileExtension', 'InUseDate.inUseDate', 'Model.created', 'Model.version',
    'PSRType.prefix', 'RatioTapChangerTable.points', 'Season.endDate',
    'Season.startDate', 'SensorWinding.accuracyClass', 'Shift.endTime', 'Shift.startTime',
    'VCTimeSpan.endTime', 'VCTimeSpan.startTime', 'VCValidityPeriod.endDate',
    'VCValidityPeriod.startDate',
}
IDENTIFIER_FIELDS = {
    'mrid', 'mridstr', 'fiasid', 'fiasstreetid', 'serialnumber', 'inventorynumber',
    'inventoryno', 'personnelnumber', 'employeeid', 'staffnumber', 'taxid',
    'inn', 'kpp', 'ogrn', 'snils', 'passport', 'passportnumber', 'passportseries',
    'contract', 'contractnumber', 'agreementnumber', 'accountnumber',
    'personalaccount', 'licence', 'licensenumber', 'taxregistrationnumber',
    'meteringpointcode', 'ccscode', 'nameplate', 'dispatchnumber',
    'inventorycode', 'registrationnumber', 'documentnumber', 'taxnumber',
    'identificationnumber', 'customernumber', 'nationalid', 'idnumber',
    'postalcode', 'postcode', 'zipcode', 'companynumber', 'commonaddress',
    'addrstr1', 'buildingnumber', 'apartmentnumber', 'pobox',
    'suitenumber',
    'tabnumber', 'taxpayerid', 'policynumber', 'omsnumber',
    'accountid', 'contractid', 'meterid', 'subscriberid', 'billingaccount',
    'dispatchcode', 'cadastralnumber', 'objectnumber', 'meterreading', 'readingvalue',
    'bankaccountnumber', 'bik', 'korrschet', 'personid', 'birthcertificate',
}
MASK_FIELDS = {
    'description', 'comment', 'comments', 'notes', 'note', 'remark', 'remarks',
    'log', 'logtext', 'message', 'text', 'markertext', 'djrecordtext',
    'texttemplate', 'signature', 'username', 'login', 'password',
    'birthdate', 'dateofbirth', 'issuedby', 'passportissuer', 'website', 'url',
    'filename', 'filepath', 'attachment', 'attachmentdata',
    'personaldata', 'biography', 'attachmentname', 'logentry', 'content',
}
ADDRESS_FIELDS = {
    'address', 'addressgeneral', 'country', 'stateorprovince', 'city',
    'town', 'buildingname', 'street', 'district', 'county', 'addressline',
    'addressline1', 'addressline2', 'postaladdress', 'registeredaddress',
}
DIAGRAM_LABELS = {
    'description', 'name', 'text', 'elementname', 'itemname', 'caption',
    'label', 'tooltip', 'header', 'title', 'tag', 'comment', 'address',
}
DIAGRAM_SYMBOLS = {
    ('textstyle', 'name'), ('strokestyle', 'name'), ('prop', 'name'), ('link', 'itemname'),
}
DIAGRAM_TERMINALS = {
    ('psrterminal', 'name'), ('tsterminal', 'name'), ('connectedorigin', 'terminal'),
    ('connecteddestination', 'terminal'), ('familiar', 'terminal'),
}
LOCAL_REFERENCE = re.compile(r'(?:#_?|urn:uuid:|_)?(' + GUID.pattern + r')\Z', re.I)
SAFE_MEMBER = re.compile(
    r'(?:\[Content_Types\]\.xml|(?:[\w.-]+/)*(?:\.rels|[\w.-]+\.(?:xml|rels|png|bmp|jpe?g|gif|ico|scrap)))\Z', re.I
)
COORDS = {'latitude', 'longitude', 'xposition', 'yposition', 'zposition', 'coordinates'}
SAFE_PI = {'iec61970-552': 'version="2.0"', 'floatExporter': '1'}
SCHEMA_URIS = (
    'http://iec.ch/TC57/', 'http://monitel.com/2014/schema-cim16#',
    'http://gost.ru/2019/schema-cim01#', 'http://rushydro.ru/2015/schema-cim16#',
    'http://so-ups.ru/2015/schema-cim16#', 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
)
SCHEMA_SYMBOL = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*')
URI_SCHEME = re.compile(r'[a-z][a-z0-9+.-]*:', re.I)
STATION_TYPE = re.compile(r'(?<![А-ЯЁ])(?:БКТП|КТПН|КТП|РТП|ТП|РП)(?![А-ЯЁ])', re.I)
EQUIPMENT_NUMBER = re.compile(r'(?:ЛЭП|БКТП|КТПН|КТП|РТП|ТП|ПС|РП)[\s№-]*([0-9]+)(?![0-9.,])', re.I)
FORMULA_FIELDS = {'Expression.formula', 'FormulaTemplate.formula'}
OPERAND_OWNER = {'Operand.Expression', 'BaseTemplateOperand.ExpressionTemplate'}
FORMULA_SYMBOL = re.compile(r'''"(?:[^"\\]|\\.)*"|'(?:[^'\\]|\\.)*'|(?<![\w.])[^\W\d]\w*''')
WORD = re.compile(r'\w+')
HTTP_URL = re.compile(r'https?://[^\s<>"\x27]+', re.I)
QUANTITY = re.compile(
    r'(?<!\w)[+-]?\d+(?:[.,]\d+)?\s*(?:кВАр|кВА|МВА|кВт|МВт|кВ|мА|Гц|Ом|мм²|км|В|А|kVAr|kVA|MVA|kW|MW|kV|mA|Hz|V|A)(?!\w)',
    re.IGNORECASE,
)
FREE_TEXT_FIELDS = {
    'description', 'comment', 'comments', 'notes', 'note', 'remark', 'remarks',
    'log', 'logtext', 'message', 'text', 'markertext', 'djrecordtext',
    'texttemplate', 'logentry', 'content', 'details', 'customnote',
}
MENTIONS = re.compile(
    r'(?P<url>' + HTTP_URL.pattern + r')'
    r'|(?P<email>(?<![\w.+-])[\w.!#$%&\x27*+/=?^_\x60{|}~-]+@(?:[\w-]+\.)+[\w-]{2,})'
    r'|(?P<guid>' + GUID.pattern + r')'
    r'|(?P<phone>(?<!\w)(?:\+7|8)[ -]*(?:\(\d{3}\)|\d{3})[ -]*\d{3}[ -]*\d{2}[ -]*\d{2}(?!\w))'
    r'|(?P<document>(?<!\w)(?i:ИНН|КПП|СНИЛС|ОГРН(?:ИП)?|паспорт|(?:лицевой|л/с)\s*(?:сч[её]т)?|таб(?:ельный)?\.?\s*(?:номер)?|договор|инв(?:ентарный)?\.?\s*(?:номер)?|тел(?:ефон)?\.?)'
    r'\s*[№:=#-]?\s*\+?\d[\d -]*\d)(?!\w)'
    r'|(?P<equipment>(?<!\w)(?i:ЛЭП|БКТП|КТПН|КТП|РТП|ТП|ПС|РП|TP|PS|RP|LEP)[\s№-]*\d+(?:[-/]\d+)*(?!\w))'
    r'|(?P<person>(?<!\w)[А-ЯЁ][а-яё-]+[ \t]+(?:[А-ЯЁ][а-яё-]+[ \t]+'
    r'[А-ЯЁ][а-яё-]*(?:ич(?:ем|ом|[ауеи])?|н(?:а|ы|е|у|ой|ою))|[А-ЯЁ]\.[ \t]*[А-ЯЁ]\.))(?!\w)'
    r'|(?P<organization>(?<!\w)(?i:ООО|АО|ПАО|ОАО|ЗАО|НКО|ИП)\s*[«"][^»"\r\n]{1,100}[»"])'
    r'|(?P<street>(?<!\w)(?i:ул\.|улица|проспект|пер\.|переулок|шоссе)\s+[А-ЯЁ][а-яё-]+'
    r'(?:[ \t]+[А-ЯЁ][а-яё-]+)?(?:\s*,?\s*(?i:д\.|дом)\s*\d+[А-Яа-яA-Za-z]?)?)',
)


def alias_key(value):
    return ' '.join(value.casefold().split())


@functools.lru_cache(maxsize=8192)
def mention_pattern(label):
    return re.compile(r'(?<!\w)' + r'\s+'.join(re.escape(word) for word in label.split()) + r'(?!\w)', re.I)


def configuration(path):
    defaults = {
        'language': 'ru', 'people': PEOPLE,
        'adjectives': [(word, word[:-2] + ('яя' if word.endswith('ий') else 'ая')) for _, word in PRODUCE],
        'class_labels': {**CLASS_LABELS, 'ТП': 'ТП', 'РП': 'РП', 'ЛЭП Section': 'Участок ЛЭП'},
        'street_prefix': 'ул.', 'number_prefix': '№', 'public_hosts': [],
    }
    if path is None:
        return defaults
    with path.open(encoding='utf-8-sig') as stream:
        overrides = json.load(stream)
    if not isinstance(overrides, dict) or overrides.keys() - defaults.keys():
        raise ValueError('Unknown or invalid configuration keys.')
    if overrides.get('language', 'ru') != 'ru' and not {
        'people', 'adjectives', 'class_labels', 'street_prefix', 'number_prefix'
    } <= overrides.keys():
        raise ValueError('For another language, provide people, adjectives, class_labels, street_prefix and number_prefix.')
    defaults.update(overrides)
    for name, width in (('people', 5), ('adjectives', 2)):
        rows = defaults[name]
        if not rows or not isinstance(rows, (list, tuple)) or any(
            not isinstance(row, (list, tuple)) or len(row) != width
            or any(not isinstance(cell, str) or not cell.strip() for cell in row)
            for row in rows
        ):
            raise ValueError(f'{name} must contain rows of {width} nonempty strings.')
    labels = defaults['class_labels']
    if not isinstance(labels, dict) or any(not isinstance(value, str) for value in labels.values()):
        raise ValueError('class_labels must map class names to strings.')
    if any(not isinstance(defaults[name], str) for name in ('language', 'street_prefix', 'number_prefix')):
        raise ValueError('Language and prefixes must be strings.')
    hosts = defaults['public_hosts']
    if not isinstance(hosts, list) or any(not isinstance(host, str) or not host for host in hosts):
        raise ValueError('public_hosts must be a list of hostnames.')
    return defaults


class TextAliases:
    def __init__(self):
        self.values = {}
        self.widths = {}

    def add(self, value, person=False, identity=''):
        source = alias_key(value)
        words = tuple(WORD.finditer(source))
        if (not 4 <= len(source) <= 180 or not 1 <= len(words) <= 12
                or not any(char.isalpha() for char in source)
                or QUANTITY.fullmatch(source)):
            return
        start = words[0][0]
        if words[0].start() != 0:
            return
        prior_person, prior_id = self.values.get(source, (False, identity))
        self.values[source] = (prior_person or person, prior_id if prior_id == identity else '')
        self.widths[start] = max(self.widths.get(start, 0), len(words))

    def matches(self, value):
        if not self.values:
            return
        words = tuple(WORD.finditer(value))
        for index, word in enumerate(words):
            width = self.widths.get(word[0].casefold(), 0)
            for end in range(min(index + width, len(words)) - 1, index - 1, -1):
                candidate = value[word.start():words[end].end()]
                key = alias_key(candidate)
                if key in self.values:
                    yield word.start(), words[end].end(), 'alias'
                    break


@functools.lru_cache(maxsize=4096)
def local(tag):
    return tag.rsplit('}', 1)[-1]


@functools.lru_cache(maxsize=4096)
def field_name(prop):
    return re.sub(r'[^a-z0-9]', '', prop.rsplit('.', 1)[-1].lower())


def rdf_key(value, attribute):
    if attribute == RDF + 'nodeID':
        return '_:' + value
    if attribute == RDF + 'ID':
        return '#' + value
    return value


def object_identity(record):
    return next((rdf_key(value, key) for key, value in record.attrib.items() if key in RDF_IDS), '')


def schema_reference(value, nsmap):
    if any(value.startswith(uri) for uri in SCHEMA_URIS):
        return bool(SCHEMA_SYMBOL.fullmatch(value.rsplit('#', 1)[-1]))
    prefix, _, symbol = value.partition(':')
    namespace = nsmap.get(prefix, '')
    return namespace.startswith(SCHEMA_URIS) and bool(SCHEMA_SYMBOL.fullmatch(symbol))


def local_reference(value):
    return not URI_SCHEME.match(value) or bool(LOCAL_REFERENCE.fullmatch(value))


def select_key(path, create):
    if create:
        try:
            with path.open('xb') as stream:
                stream.write(secrets.token_bytes(32))
        except FileExistsError:
            pass
    key = path.read_bytes()
    if len(key) != 32:
        raise ValueError('The key file must contain exactly 32 bytes.')
    return key


class Pseudonyms:
    def __init__(self, key, config=None):
        self.key = key
        self.config = config if config is not None else configuration(None)
        self.public_hosts = {host.lower() for host in self.config['public_hosts']}
        self.guid = functools.lru_cache(maxsize=200_000)(self.guid)
        self.ref = functools.lru_cache(maxsize=200_000)(self.ref)
        self.identifier = functools.lru_cache(maxsize=50_000)(self.identifier)
        self.decimal = functools.lru_cache(maxsize=32_768)(self.decimal)
        self.aliases = TextAliases()
        self.resolve_name = None
        self.related_mentions = None
        self.stats = Counter()

    def digest(self, domain, text):
        return hmac.digest(self.key, (domain + '\0' + text).encode('utf-8'), 'sha256')

    def guid(self, value):
        return str(uuid.UUID(bytes=self.digest('rdf-guid', value)[:16], version=4))

    def ref(self, value):
        if match := LOCAL_REFERENCE.fullmatch(value):
            return value[:match.start(1)] + self.guid(match[1].lower())
        if URI_SCHEME.match(value):
            return 'urn:cim-anonymized:' + self.token('absolute-rdf-id', value, length=20)
        prefix = '#' if value.startswith('#') else ''
        return prefix + 'anon_' + self.token('rdf-id', value.removeprefix('#'), length=20)

    def token(self, domain, value, length=12):
        return base64.b32encode(self.digest(domain, value)[:length]).decode('ascii').rstrip('=')

    def person(self, value):
        names = self.config['people']
        return names[int.from_bytes(self.digest('person', value)[:4], 'big') % len(names)]

    def adjective(self, value, feminine=False):
        words = self.config['adjectives']
        return words[int.from_bytes(self.digest('produce', value)[:4], 'big') % len(words)][feminine]

    def label(self, value, prefix='', identity=None, role=None):
        suffix = self.token('object-label', identity) if identity else self.token('label', value)
        adjective = self.adjective(value, prefix in {'ПС', 'ТП', 'ЛЭП', 'Опора', 'Секция шин', 'Обмотка'})
        number = EQUIPMENT_NUMBER.search(value) if prefix in {'ПС', 'ТП', 'РП', 'ЛЭП'} else None
        synthetic = f'{adjective} {suffix}'
        if number:
            synthetic += f' {self.config["number_prefix"]}{self.decimal(number[1])}'
        prefix = self.config['class_labels'].get(role or prefix, prefix if self.config['language'] == 'ru' else '')
        return f'{prefix} {synthetic}' if prefix else synthetic

    def full_name(self, seed, unique=False):
        first, last, patronymic, _, _ = self.person(seed)
        name = f'{last} {first} {patronymic}'
        return f'{name} ({self.token("person-label", seed)})' if unique else name

    def formula_symbol(self, seed):
        return 'V_' + self.token('formula-symbol', seed)

    def date(self, value):
        try:
            original = date.fromisoformat(value[:10])
        except ValueError:
            return self.identifier(value)
        days = 365 * 10
        offset = 1 + int.from_bytes(self.digest('personal-date', value)[:4], 'big') % days
        ordinal = (original.toordinal() - 1 + offset) % date.max.toordinal() + 1
        date_part = date.fromordinal(ordinal).isoformat()
        if len(value) == 10:
            return date_part
        try:
            datetime.fromisoformat(value)
        except ValueError:
            return self.identifier(value)
        return date_part + value[10:11] + '00:00:00Z'

    def decimal(self, value):
        width = len(value)
        if width == 1:
            offset = 1 + self.digest('digit', 'v1')[0] % 9
            return str((int(value) + offset) % 10)
        widths = (width // 2, width - width // 2)
        limits = tuple(10 ** count for count in widths)

        def mix(round_number, digit_string):
            scope = f'decimal:{width}:{round_number}'
            return int.from_bytes(self.digest(scope, digit_string), 'big')

        left, right = int(value[:widths[0]]), int(value[widths[0]:])
        for step in range(8):
            side = step % 2
            if side == 0:
                left = (left + mix(step, str(right))) % limits[0]
            else:
                right = (right + mix(step, str(left))) % limits[1]
        right ^= 1
        for step in reversed(range(8)):
            side = step % 2
            if side == 0:
                left = (left - mix(step, str(right))) % limits[0]
            else:
                right = (right - mix(step, str(left))) % limits[1]
        return str(left).zfill(widths[0]) + str(right).zfill(widths[1])

    def identifier(self, value):
        if LOCAL_REFERENCE.fullmatch(value):
            return self.ref(value)
        if DECIMAL.fullmatch(value):
            return self.decimal(value)
        # Replace letters and retain the widths of decimal components.
        groups = DECIMAL.findall(value)
        suffix = '-' + '-'.join(self.decimal(group) for group in groups) if groups else ''
        return 'ID-' + self.token('identifier', value) + suffix

    def free_text(self, value, *, linked=False):
        if self.resolve_name is not None and (exact := self.resolve_name(alias_key(value), '', exact=True)):
            return exact
        protected = list(PLACEHOLDER.finditer(value)) + list(QUANTITY.finditer(value))
        related = []
        if linked and self.related_mentions is not None:
            candidates = sorted(self.related_mentions(value), key=lambda hit: (hit[0], -hit[1]))
            for left, right, replacement in candidates:
                if related and left < related[-1][1]:
                    continue
                # Retain formatting tokens and measurements that cross the name boundary.
                if any(left < span.end() and right > span.start() and (
                    span.re is PLACEHOLDER or span.start() < left or span.end() > right
                ) for span in protected):
                    continue
                related.append((left, right, replacement))
        hits = [(left, right, 'alias', None) for left, right, _ in self.aliases.matches(value)]
        hits.extend((match.start(), match.end(), match.lastgroup, None) for match in MENTIONS.finditer(value))
        if related:
            hits = [hit for hit in hits if all(hit[1] <= left or hit[0] >= right for left, right, _ in related)]
            hits.extend((left, right, 'related', replacement) for left, right, replacement in related)
        hits.sort(key=lambda hit: (hit[0], -hit[1], hit[2] != 'alias'))
        start = 0
        parts = []
        for left, right, kind, replacement in hits:
            if left < start:
                continue
            overlapping = [span for span in protected if left < span.end() and right > span.start()]
            if overlapping and kind != 'related' and (kind != 'alias' or any(
                not left < span.start() or span.end() > right for span in overlapping
            )):
                continue
            original = value[left:right]
            parts.append(value[start:left])
            parts.append(replacement if kind == 'related' else self.replace_mention(original, kind))
            if kind == 'related':
                self.stats['linked_name_mentions'] += 1
            if overlapping:
                parts.append(' ' + ' '.join(span[0] for span in sorted(overlapping, key=lambda span: span.start())))
            start = right
        parts.append(value[start:])
        return ''.join(parts)

    def replace_mention(self, text, kind):
        if kind == 'url':
            url = text.rstrip('.,;:!?)]')
            return self.url(url) + text[len(url):]
        if kind == 'guid':
            return self.guid(text.lower())
        if kind in {'phone', 'document', 'equipment'}:
            return re.sub(r'[0-9]+', lambda match: self.decimal(match[0]), text)
        seed = alias_key(text)
        if kind == 'alias':
            person, candidate = self.aliases.values[seed]
            if self.resolve_name is not None:
                replacement = self.resolve_name(seed, candidate)
                if replacement is not None:
                    return replacement
            return self.full_name(seed) if person else self.label(seed)
        if kind == 'person':
            return self.full_name(seed)
        if kind == 'email':
            return f'{self.person(seed)[3]}.{self.token("email", seed).lower()}@example.invalid'
        if kind == 'street':
            return f'{self.config["street_prefix"]} {self.person(seed)[4]} {self.token("street", seed)}'.strip()
        return self.label(seed)

    def name_text(self, value):
        seed = alias_key(value)
        if self.resolve_name is not None:
            _, candidate = self.aliases.values.get(seed, (False, ''))
            if replacement := self.resolve_name(seed, candidate):
                return replacement
        return self.label(seed)

    def url(self, value):
        if schema_reference(value, {}):
            return value
        try:
            parts = urlsplit(value)
            host = parts.hostname
        except ValueError:
            host = None
        if host in self.public_hosts and (
            parts.path in {'', '/'} and not (parts.username or parts.password or parts.query or parts.fragment)
        ):
            return value
        return 'https://example.invalid/resource/' + self.token('external-url', value).lower()

    def embedded_refs(self, value):
        return GUID.sub(lambda match: self.guid(match[0].lower()), value)


def parser_for_embedded():
    return etree.XMLParser(
        resolve_entities=False, no_network=True, load_dtd=False, remove_comments=True,
        remove_pis=True,
    )


def embedded_xml(data, pseudonyms, diagram=False, sections=False):
    root = etree.fromstring(data, parser_for_embedded())
    if root.getroottree().docinfo.doctype:
        raise ValueError('DOCTYPE in embedded XML.')
    diagram_names = {}
    if diagram:
        for node in root.iter():
            for key, value in node.attrib.items():
                if 'name' in local(key).casefold() and value.strip():
                    diagram_names[value] = pseudonyms.name_text(value)
    for node in root.iter():
        tag = local(node.tag).lower()
        for key, value in node.attrib.items():
            field = local(key).lower()
            if not value.strip():
                continue
            if tag == 'relationship' and field == 'target' and node.get('TargetMode') == 'External':
                node.set(key, pseudonyms.url(value) if HTTP_URL.fullmatch(value) else 'about:blank')
            elif sections and field == 'nameplate':
                node.set(key, pseudonyms.identifier(value))
            elif sections and field == 'name':
                node.set(key, pseudonyms.label(value, 'Участок ЛЭП', role='ЛЭП Section'))
            elif diagram and 'name' in field:
                node.set(key, diagram_names[value])
            elif diagram and (tag, field) in DIAGRAM_TERMINALS:
                if not DECIMAL.fullmatch(value):
                    node.set(key, pseudonyms.identifier(value))
            elif diagram and (tag, field) in DIAGRAM_SYMBOLS:
                node.set(key, pseudonyms.embedded_refs(value))
            elif field in DIAGRAM_LABELS and (diagram or field in {'description', 'comment', 'address'}):
                node.set(key, pseudonyms.free_text(value))
            elif diagram and value in diagram_names and ('style' in field or 'ref' in field):
                node.set(key, diagram_names[value])
            else:
                node.set(key, pseudonyms.embedded_refs(value))
        if node.text and node.text.strip():
            if (diagram or sections) and 'name' in tag:
                node.text = pseudonyms.name_text(node.text)
            elif diagram or tag in DIAGRAM_LABELS:
                node.text = pseudonyms.free_text(node.text)
            else:
                node.text = pseudonyms.embedded_refs(node.text)
        if node.tail and node.tail.strip():
            node.tail = pseudonyms.free_text(node.tail)
    return etree.tostring(root, encoding='UTF-8', xml_declaration=True)


def raster_attachment(data, pseudonyms):
    stats = pseudonyms.stats
    image_format = 'PNG'
    safe_pixels = None
    try:
        with Image.open(io.BytesIO(data)) as image:
            image_format = image.format or 'PNG'
            stats['binary_type_' + image_format.lower()] += 1
            for value in image.info.values():
                if isinstance(value, str) and pseudonyms.free_text(value) != value:
                    stats['raster_metadata_sensitive'] += 1
            if getattr(image, 'n_frames', 1) == 1 and image.width * image.height <= 12_000_000:
                colors = image.convert('RGB').getcolors(maxcolors=1)
                if colors:
                    safe_pixels = (image.size, colors[0][1])
    except (OSError, Image.DecompressionBombError):
        stats['raster_unreadable'] += 1
    if safe_pixels is None:
        stats['raster_placeholders'] += 1
        size = (32, 32) if image_format == 'ICO' else (1, 1)
        safe_pixels = (size, (255, 255, 255))
    else:
        stats['raster_blank_verified'] += 1
    output = io.BytesIO()
    bitmap = Image.new('RGB', *safe_pixels)
    if image_format not in Image.SAVE:
        Image.init()
    bitmap.save(output, format=image_format if image_format in Image.SAVE else 'PNG')
    return output.getvalue()


def diagram_archive(data, pseudonyms, depth=0):
    if depth > 4:
        raise ValueError('Excessive nesting in diagram package.')
    output = io.BytesIO()
    pseudonyms.stats['binary_type_zip'] += 1
    with ZipFile(io.BytesIO(data)) as original, ZipFile(output, 'w') as sanitized:
        for member in original.infolist():
            name = member.filename
            if not SAFE_MEMBER.fullmatch(name) or '..' in name.split('/') or member.file_size > 64 * 1024 * 1024:
                raise ValueError('Unexpected member in diagram package.')
            content = original.read(member)
            if name.lower().endswith('.scrap'):
                content = diagram_archive(content, pseudonyms, depth + 1)
            elif name.lower().endswith(('.xml', '.rels')):
                diagram = name.lower().endswith('.xml') and name != '[Content_Types].xml'
                content = embedded_xml(content, pseudonyms, diagram=diagram)
            else:
                content = raster_attachment(content, pseudonyms)
            info = ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
            sanitized.writestr(info, content, compress_type=ZIP_DEFLATED)
    return output.getvalue()


def audio_attachment(data, pseudonyms):
    stats = pseudonyms.stats
    params = (1, 2, 8000, 0, 'NONE', 'not compressed')
    frames = b'\0' * 1600
    verified_silent = False
    if data.startswith(b'RIFF') and data[8:12] == b'WAVE':
        stats['binary_type_wave'] += 1
        try:
            with wave.open(io.BytesIO(data), 'rb') as source:
                original = source.readframes(source.getnframes())
                neutral = 128 if source.getsampwidth() == 1 else 0
                if original == bytes([neutral]) * len(original):
                    params = source.getparams()
                    frames = original
                    verified_silent = True
        except (EOFError, OSError, wave.Error):
            pass
    else:
        signatures = ((b'OggS', 'ogg'), (b'fLaC', 'flac'), (b'ID3', 'mp3'))
        kind = next((label for signature, label in signatures if data.startswith(signature)), 'unknown_audio')
        stats['binary_type_' + kind] += 1
    stats['audio_silent_verified' if verified_silent else 'audio_placeholders'] += 1
    output = io.BytesIO()
    with wave.open(output, 'wb') as sound:
        sound.setparams(params)
        sound.writeframes(frames)
    return output.getvalue()


def generic_attachment(data, pseudonyms):
    try:
        text = data.decode('utf-8-sig')
    except UnicodeDecodeError:
        text = ''
    if text.lstrip().startswith('<'):
        pseudonyms.stats['binary_type_xml'] += 1
        return embedded_xml(data, pseudonyms, diagram=True)
    if text and all(char.isprintable() or char in '\r\n\t' for char in text):
        pseudonyms.stats['binary_type_text'] += 1
        return pseudonyms.free_text(text).encode('utf-8')
    pseudonyms.stats['binary_type_opaque'] += 1
    return b'REDACTED'


class Transformer:
    def __init__(self, key, coordinates=False, catalog=None, config=None):
        self.pseudonyms = Pseudonyms(key, config)
        self.coordinates = coordinates
        self.stats = self.pseudonyms.stats
        self.classes = Counter()
        self.index = None
        self.catalog = catalog or ModelCatalog()
        self.pseudonyms.aliases = self.catalog.aliases
        self.pseudonyms.resolve_name = self.resolve_name
        self.pseudonyms.related_mentions = self.related_mentions
        self.current_record = None
        self.context_names = None
        self.referenced_names = None

    def primary_name(self, identity, value, cls, individual):
        p = self.pseudonyms
        if identity in self.catalog.operands:
            return p.formula_symbol(identity)
        if individual:
            return p.full_name(identity or value, unique=True)
        prefix, role = CLASS_LABELS.get(cls, ''), cls
        if cls == 'Substation' and (match := STATION_TYPE.search(value.upper())):
            prefix = 'РП' if match[0] == 'РП' else 'ТП'
            role = prefix
        return p.label(value, prefix, identity, role)

    def names_in_references(self):
        if self.current_record is None:
            return {}
        if self.referenced_names is None:
            self.referenced_names = {}
            for target in {node.get(RDF_VALUE) for node in self.current_record.iter()}:
                if target in self.catalog.primary_names:
                    seed = alias_key(self.catalog.primary_names[target][0])
                    prior = self.referenced_names.setdefault(seed, target)
                    if prior != target:
                        self.referenced_names[seed] = ''
        return self.referenced_names

    def names_in_context(self):
        if self.current_record is None:
            return {}
        if self.context_names is None:
            self.context_names = self.names_in_references().copy()
            owner = object_identity(self.current_record)
            if owner in self.catalog.primary_names:
                seed = alias_key(self.catalog.primary_names[owner][0])
                if self.context_names.setdefault(seed, owner) != owner:
                    self.context_names[seed] = ''
        return self.context_names

    def related_mentions(self, value):
        normalized = alias_key(value)
        references = self.names_in_references()
        linked = [
            hit for seed, target in references.items()
            for hit in self.match_name_mention(value, normalized, seed, target)
        ]
        yield from linked
        for seed, target in self.names_in_context().items():
            if seed in references:
                continue
            for left, right, replacement in self.match_name_mention(value, normalized, seed, target):
                if all(right <= start or left >= end for start, end, _ in linked):
                    yield left, right, replacement

    def match_name_mention(self, value, normalized, seed, target):
        if not target or len(seed) < 4 or seed not in normalized or not any(c.isalpha() for c in seed):
            return
        matches = list(mention_pattern(seed).finditer(value))
        if matches:
            replacement = self.resolve_name(seed, target)
            for match in matches:
                yield match.start(), match.end(), replacement

    def resolve_name(self, seed, candidate, exact=False):
        if not candidate and seed in self.catalog.name_keys:
            candidate = self.names_in_context().get(seed, '')
            if not candidate and not exact:
                candidate = self.catalog.aliases.values.get(seed, (False, ''))[1]
        if candidate and candidate in self.catalog.primary_names:
            raw, cls = self.catalog.primary_names[candidate]
            return self.primary_name(candidate, raw, cls, self.catalog.individual(cls, candidate, raw))
        return None

    def record(self, record):
        etree.strip_elements(record, etree.ProcessingInstruction, with_tail=False)
        object_class = local(record.tag)
        self.classes[record.tag] += 1
        identity = object_identity(record)
        self.current_record = record
        self.context_names = None
        self.referenced_names = None
        raw_name = self.catalog.primary_names.get(identity, ('', ''))[0]
        individual = self.catalog.individual(object_class, identity, raw_name)
        if object_class == 'Customer':
            self.stats['customer_' + ('individual' if individual else 'other_or_unspecified')] += 1

        remapped = []
        for node in record.iter():
            for attribute, value in node.attrib.items():
                if attribute == XML_BASE:
                    raise ValueError('xml:base is not supported for this CIM profile')
                if attribute in RDF_IDS:
                    mapped = self.pseudonyms.ref(value)
                    remapped.append((node, attribute, mapped))
                    self.stats['definitions'] += 1
                    if self.index is not None and (node is record or attribute != RDF + 'nodeID'):
                        self.index.definition(rdf_key(value, attribute), rdf_key(mapped, attribute))
                elif attribute == RDF_VALUE:
                    is_local = local_reference(value)
                    is_schema = ':' in value and schema_reference(value, node.nsmap)
                    if value and (value in self.catalog.absolute_ids or (is_local and not is_schema)):
                        mapped = self.pseudonyms.ref(value)
                        remapped.append((node, attribute, mapped))
                        self.stats['references'] += 1
                        if self.index is not None:
                            self.index.reference(value, mapped, is_local)
                    elif not is_schema and HTTP_URL.fullmatch(value):
                        mapped = self.pseudonyms.url(value)
                        remapped.append((node, attribute, mapped))
                        self.stats['external_links_masked' if mapped != value else 'external_links_kept'] += 1
                        if self.index is not None:
                            self.index.reference(value, mapped, False)
                    else:
                        self.stats['preserved_schema_or_external_references'] += 1
                elif value.strip() and attribute not in TECHNICAL_ATTRIBUTES:
                    prop = local(attribute)
                    replacement = self.literal(prop, object_class, individual, identity, value)
                    if 'name' in field_name(prop) and prop not in CLASSIFIER_FIELDS:
                        self.stats['name_fields_changed'] += replacement != value
                        if replacement == value:
                            raise ValueError(f'Name attribute was not changed: {prop}')
                    node.set(attribute, replacement)
            if node.text and node.text.strip():
                value = node.text.strip()
                prop = local(node.tag)
                replaced = self.literal(prop, object_class, individual, identity, value)
                if replaced != value:
                    self.stats['modified_literals'] += 1
                    node.text = replaced
                if 'name' in field_name(prop) and prop not in CLASSIFIER_FIELDS:
                    self.stats['name_fields_changed'] += replaced != value
                    if replaced == value:
                        raise ValueError(f'Name field was not changed: {prop}')
                if self.index is not None and prop == 'IdentifiedObject.name':
                    self.index.name(replaced, identity or value)
            if node is not record and node.tail and node.tail.strip():
                node.tail = self.pseudonyms.free_text(node.tail)
        for node, attribute, mapped in remapped:
            node.set(attribute, mapped)
        self.current_record = None

    def literal(self, prop, cls, individual, identity, value):
        p = self.pseudonyms
        owner = prop.rpartition('.')[0]
        lower = field_name(prop)
        if prop in CLASSIFIER_FIELDS:
            self.stats['classifier_values_preserved'] += 1
            return value
        if prop == 'MonitelDiagram.image':
            self.stats['diagram_packages'] += 1
            return base64.b64encode(diagram_archive(base64.b64decode(value), p)).decode('ascii')
        if prop in {'BlobStorage.image', 'MarkerType.diagramView', 'MarkerType.additionalView'}:
            self.stats['raster_attachments'] += 1
            data = raster_attachment(base64.b64decode(value), p)
            return base64.b64encode(data).decode('ascii')
        if prop == 'EventSound.sound':
            self.stats['audio_attachments'] += 1
            return base64.b64encode(audio_attachment(base64.b64decode(value), p)).decode('ascii')
        if prop in {'ACLineSegment.sections', 'DjCategory.allowedObjectsFilter', 'DjAttributeSet.xsd'}:
            self.stats['encoded_xml'] += 1
            self.stats['binary_type_xml'] += 1
            data = embedded_xml(base64.b64decode(value), p, sections=prop == 'ACLineSegment.sections')
            return base64.b64encode(data).decode('ascii')
        if prop == 'IdentifiedObject.name':
            return self.primary_name(identity, value, cls, individual)
        if lower in PERSON_LABELS:
            return p.full_name((identity if individual else '') or value)
        if lower in PERSON_NAME_FIELDS:
            first, last, patronymic, _, _ = p.person(identity or value)
            if lower in {'firstname', 'givenname'}:
                return first
            return last if lower in {'lastname', 'surname', 'familyname'} else patronymic
        if 'email' in lower or lower in {'mail', 'emailaddress'}:
            _, _, _, spelling, _ = p.person(identity or value)
            return f'{spelling}.{p.token("email", value).lower()}@example.invalid'
        if any(key in lower for key in ('phone', 'mobile', 'fax', 'telephone')):
            return re.sub(r'[0-9]+', lambda match: p.decimal(match[0]), value) if re.fullmatch(r'[+()0-9 .-]+', value) else p.identifier(value)
        if prop == 'StreetDetail.name' or lower in {'streetname', 'street'}:
            _, _, _, _, street = p.person((identity if individual else '') or value)
            return f'{p.config["street_prefix"]} {street} {p.token("street", value)}'.strip()
        if owner in {'StreetDetail', 'TownDetail', 'PostalAddress', 'StreetAddress', 'Address'}:
            return p.identifier(value) if lower in IDENTIFIER_FIELDS | {'number'} or DECIMAL.fullmatch(value) else p.label(value)
        if prop == 'IPConnectionPoint.address':
            try:
                address = ipaddress.ip_address(value)
            except ValueError:
                return p.label(value)
            code = int.from_bytes(p.digest('ip-address', value)[:8], 'big')
            if address.version == 4:
                networks = ('192.0.2.', '198.51.100.', '203.0.113.')
                return networks[code % 3] + str(1 + code // 3 % 254)
            return str(ipaddress.IPv6Address(int(ipaddress.IPv6Address('2001:db8::')) | code))
        if lower in ADDRESS_FIELDS:
            return p.label(value)
        if owner in {'Attachment', 'DocumentAttachment'} and lower in {'data', 'content', 'attachmentdata'}:
            try:
                data = base64.b64decode(''.join(value.split()), validate=True)
            except ValueError:
                return p.free_text(value)
            return base64.b64encode(generic_attachment(data, p)).decode('ascii')
        if owner in {'MeterReading', 'Reading', 'IntervalReading'} and lower in {'value', 'reading'}:
            return re.sub(r'[0-9]+', lambda match: p.decimal(match[0]), value) if SCALAR.fullmatch(value) else p.identifier(value)
        if lower in IDENTIFIER_FIELDS:
            return p.identifier(value)
        if 'name' in lower:
            return p.name_text(value)
        if lower in {'url', 'website', 'uri', 'href'} and HTTP_URL.fullmatch(value):
            return p.url(value)
        if lower in COORDS:
            if not self.coordinates:
                return value
            return '0' if SCALAR.fullmatch(value) else p.free_text(value)
        if lower in {'birthdate', 'dateofbirth', 'dob', 'passportissuedate'}:
            return p.date(value)
        if lower in FREE_TEXT_FIELDS or lower.endswith(('description', 'comment', 'logentry')):
            return p.free_text(value, linked=True)
        if lower in MASK_FIELDS or lower.endswith(('password', 'signature')):
            return p.label(value)
        if lower == 'designation':
            if individual:
                return p.full_name(identity or value)
            return p.label(value)
        if prop in FORMULA_FIELDS:
            return self.formula(identity, value)
        if prop == 'HISPartitionBase.prefix':
            return p.embedded_refs(value)
        if prop in TECHNICAL_TEXT or lower in {'mode', 'state', 'status', 'type', 'class'} or SCALAR.fullmatch(value):
            return value
        return p.free_text(value)

    def formula(self, identity, value):
        names = self.catalog.symbols.get(identity, {})
        pseudonyms = self.pseudonyms

        def replace(match):
            symbol = match[0]
            operand = names.get(symbol) or names.get(symbol.casefold())
            if operand:
                self.stats['formula_operand_mentions'] += 1
                return pseudonyms.formula_symbol(operand)
            return symbol

        return pseudonyms.embedded_refs(FORMULA_SYMBOL.sub(replace, value))


def open_rdf(path):
    reader = etree.iterparse(
        path, events=('start', 'end'), no_network=True, load_dtd=False,
        resolve_entities=False, remove_comments=True,
    )
    event, root = next(reader)
    if event != 'start' or root.tag != RDF + 'RDF':
        raise ValueError('Expected an rdf:RDF document.')
    if root.getroottree().docinfo.doctype:
        raise ValueError('DOCTYPE is not supported.')
    if XML_BASE in root.attrib:
        raise ValueError('xml:base is not supported for this CIM profile.')
    return root, reader


def records(root, reader):
    for event, node in reader:
        if event != 'end' or node.getparent() is not root:
            continue
        yield node
        node.clear()
        while node.getprevious() is not None:
            del root[0]


class ModelCatalog:
    def __init__(self):
        self.customer_kinds = {}
        self.operands = set()
        self.symbols = defaultdict(dict)
        self.absolute_ids = set()
        self.aliases = TextAliases()
        self.primary_names = {}
        self.name_keys = set()
        self.customers = {}

    def individual(self, cls, identity, raw_name):
        if cls != 'Customer':
            return cls in PERSON_CLASSES
        kind, kind_ref = self.customers.get(identity, ('', ''))
        if kind:
            return kind in {'residential', 'individual', 'naturalperson', 'household'}
        return self.customer_kinds.get(kind_ref, bool(PERSON_NAME.fullmatch(raw_name)))

    @classmethod
    def scan(cls, source):
        root, reader = open_rdf(source)
        result = cls()
        for record in records(root, reader):
            object_class = local(record.tag)
            identity = object_identity(record)
            if URI_SCHEME.match(identity) and not local_reference(identity):
                result.absolute_ids.add(identity)
            personal = object_class in PERSON_CLASSES
            customer_refs = {}
            for child in record:
                if not isinstance(child.tag, str):
                    continue
                field = local(child.tag)
                if object_class == 'Customer' and field in {'Customer.kind', 'Customer.OMSKind'}:
                    customer_refs[field] = child.get(RDF_VALUE, '')
                if not child.text or not child.text.strip():
                    continue
                if field == 'IdentifiedObject.name':
                    result.primary_names[identity] = (child.text.strip(), object_class)
                    result.name_keys.add(alias_key(child.text))
                    result.aliases.add(child.text, person=personal, identity=identity)
                elif field_name(field) in PERSON_LABELS or (personal and field_name(field) in PERSON_NAME_FIELDS):
                    result.aliases.add(child.text, person=True)
            if object_class == 'Customer':
                kind = customer_refs.get('Customer.kind', '').lower().rsplit('.', 1)[-1]
                result.customers[identity] = (kind, customer_refs.get('Customer.OMSKind', ''))
            if object_class != 'OMSCustomerKind' and not object_class.endswith('Operand'):
                continue
            name = next((node.text for node in record
                         if isinstance(node.tag, str) and local(node.tag) == 'IdentifiedObject.name'), '') or ''
            if not identity or not name.strip():
                continue
            if object_class == 'OMSCustomerKind':
                normalized = ' '.join(re.findall(r'[^\W_]+', name.casefold()))
                result.customer_kinds[identity] = any(part in normalized for part in (
                    'физическ', 'физ лиц', 'физлиц', 'населени', 'бытов',
                    'residential', 'natural person', 'individual',
                ))
                continue
            owner = next((node.get(RDF_VALUE) for node in record
                          if isinstance(node.tag, str) and local(node.tag) in OPERAND_OWNER), None)
            if owner:
                result.operands.add(identity)
                names = result.symbols[owner]
                names[name.strip()] = identity
                names.setdefault(name.strip().casefold(), identity)
        return result


def header_instructions(root):
    instructions = []
    sibling = root.getprevious()
    while sibling is not None:
        if isinstance(sibling, etree._ProcessingInstruction) and SAFE_PI.get(sibling.target) == sibling.text:
            instructions.append(sibling)
        sibling = sibling.getprevious()
    return reversed(instructions)


def serialized_text(value):
    return escape(value).replace('\r', '&#13;').replace('\n', '&#10;')


def element_name(node):
    return f'{node.prefix}:{local(node.tag)}' if node.prefix else local(node.tag)


def opening_tag(node, parent_ns):
    tag = element_name(node)
    attributes = {}
    nsmap = node.nsmap
    for prefix, uri in nsmap.items():
        if parent_ns.get(prefix) != uri:
            attributes[f'xmlns:{prefix}' if prefix else 'xmlns'] = uri
    if node.attrib:
        prefixes = {uri: prefix for prefix, uri in nsmap.items() if prefix}
        prefixes['http://www.w3.org/XML/1998/namespace'] = 'xml'
        for key, value in node.attrib.items():
            if key.startswith('{'):
                namespace, name = key[1:].split('}', 1)
                key = f'{prefixes[namespace]}:{name}'
            attributes[key] = value
    start = '<' + tag + ''.join(f' {key}={quoteattr(value)}' for key, value in attributes.items())
    return start, tag, nsmap


def write_record(writer, node, parent_ns, depth=1, inline=False):
    indent = '  ' * depth
    start, tag, nsmap = opening_tag(node, parent_ns)
    padding = '' if inline or depth == 1 else indent
    newline = '' if inline else '\n'
    if len(node) == 0:
        if node.text:
            writer.write(f'{padding}{start}>{serialized_text(node.text)}</{tag}>{newline}')
        else:
            writer.write(f'{padding}{start}/>{newline}')
        return
    mixed = (
        inline or node.get(XML_SPACE) == 'preserve' or bool((node.text or '').strip())
        or any((child.tail or '').strip() for child in node)
    )
    if mixed:
        writer.write(f'{padding}{start}>' + serialized_text(node.text or ''))
        for child in node:
            write_record(writer, child, nsmap, depth + 1, inline=True)
            if child.tail:
                writer.write(serialized_text(child.tail))
        writer.write(f'</{tag}>{newline}')
    else:
        writer.write(f'{padding}{start}>\n')
        for child in node:
            write_record(writer, child, nsmap, depth + 1)
        writer.write(f'{indent}</{tag}>{newline}')


def transform(source, destination, transformer):
    root, reader = open_rdf(source)
    root_ns = root.nsmap
    if set(root.attrib) - TECHNICAL_ATTRIBUTES:
        raise ValueError('Unexpected attribute on the rdf:RDF root.')
    with destination.open('w', encoding='utf-8', newline='\n', buffering=1024 * 1024) as writer:
        writer.write("<?xml version='1.0' encoding='UTF-8'?>\n")
        for instruction in header_instructions(root):
            writer.write(etree.tostring(instruction, encoding='unicode', with_tail=False))
        start, tag, _ = opening_tag(root, {})
        writer.write(start + '>\n')
        for index, record in enumerate(records(root, reader), 1):
            try:
                transformer.record(record)
            except (ValueError, OSError, etree.LxmlError, BadZipFile) as exc:
                raise ValueError(f'Record {index}, type {local(record.tag)}: {type(exc).__name__} while sanitizing payload.') from None
            write_record(writer, record, root_ns)
            if index % 100_000 == 0:
                print(f'Transformed {index:,} records', file=sys.stderr, flush=True)
        writer.write(f'</{tag}>\n')


def equivalent(left, right):
    if left.tag != right.tag or left.attrib != right.attrib:
        return False
    if (left.text or '') != (right.text or ''):
        if len(left) == 0 or len(right) == 0 or (left.text or '').strip() != (right.text or '').strip():
            return False
    if len(left) != len(right):
        return False
    for a, b in zip(left, right):
        if (a.tail or '').strip() != (b.tail or '').strip() or not equivalent(a, b):
            return False
    return True


class GraphIndex:
    def __init__(self, db):
        self.db = db
        self.db.executescript('''
            PRAGMA journal_mode = OFF;
            PRAGMA synchronous = OFF;
            PRAGMA cache_size = -32768;
            CREATE TABLE definitions (source TEXT PRIMARY KEY, result TEXT NOT NULL UNIQUE);
            CREATE TABLE refs (source TEXT PRIMARY KEY, result TEXT NOT NULL UNIQUE, local INTEGER NOT NULL);
            CREATE TABLE names (result TEXT PRIMARY KEY, source TEXT NOT NULL);
        ''')
        self.batches = {'definitions': {}, 'refs': {}, 'names': {}}

    def remember(self, table, key, fields):
        batch = self.batches[table]
        previous = batch.setdefault(key, fields)
        if previous != fields:
            raise ValueError(f'Inconsistent mapping in {table}.')
        if len(batch) >= 20_000:
            self.flush(table)

    def definition(self, original, changed):
        self.remember('definitions', original, (changed,))

    def reference(self, original, changed, is_local):
        self.remember('refs', original, (changed, is_local))

    def name(self, changed, original):
        self.remember('names', changed, (original,))

    def flush(self, table):
        batch = self.batches[table]
        if not batch:
            return
        statement = {
            'definitions': '''
                INSERT INTO definitions VALUES (?, ?) ON CONFLICT(source) DO UPDATE
                SET result = NULL WHERE result IS NOT excluded.result
            ''',
            'refs': '''
                INSERT INTO refs VALUES (?, ?, ?) ON CONFLICT(source) DO UPDATE
                SET result = NULL WHERE result IS NOT excluded.result OR local IS NOT excluded.local
            ''',
            'names': '''
                INSERT INTO names VALUES (?, ?) ON CONFLICT(result) DO UPDATE
                SET source = NULL WHERE source IS NOT excluded.source
            ''',
        }[table]
        try:
            self.db.executemany(statement, ((key, *batch[key]) for key in sorted(batch)))
        except sqlite3.IntegrityError:
            raise ValueError(f'Pseudonym collision or inconsistent mapping in {table}.') from None
        batch.clear()

    def summary(self):
        for table in self.batches:
            self.flush(table)
        mismatch = self.db.execute('''
            SELECT 1 FROM refs AS r
            LEFT JOIN definitions AS input ON input.source = r.source
            LEFT JOIN definitions AS output ON output.result = r.result
            WHERE input.source IS NOT output.source LIMIT 1
        ''').fetchone()
        if mismatch:
            raise ValueError('An RDF reference changed its target or resolution status.')
        return {
            'unique_rdf_ids': self.db.execute('SELECT count(*) FROM definitions').fetchone()[0],
            'unique_generated_object_names': self.db.execute('SELECT count(*) FROM names').fetchone()[0],
            'local_reference_targets': self.db.execute('SELECT count(*) FROM refs WHERE local').fetchone()[0],
            'local_targets_without_definition_in_both_files': self.db.execute('''
                SELECT count(*) FROM refs LEFT JOIN definitions USING (source)
                WHERE refs.local AND definitions.source IS NULL
            ''').fetchone()[0],
        }


def verify(source, result, transformer):
    root_input, reader_input = open_rdf(source)
    root_output, reader_output = open_rdf(result)
    if root_input.attrib != root_output.attrib or root_input.nsmap != root_output.nsmap:
        raise ValueError('Root XML attributes or namespace bindings differ.')
    expected_pi = [(node.target, node.text) for node in header_instructions(root_input)]
    actual_pi = [(node.target, node.text) for node in header_instructions(root_output)]
    if expected_pi != actual_pi:
        raise ValueError('CIM processing instructions differ.')
    with TemporaryDirectory(prefix='cim-verify-') as directory:
        db = sqlite3.connect(Path(directory) / 'graph.sqlite3')
        try:
            transformer.index = GraphIndex(db)
            pairs = zip_longest(records(root_input, reader_input), records(root_output, reader_output))
            for index, (original, output) in enumerate(pairs, 1):
                if original is None or output is None:
                    raise ValueError('Different record counts.')
                transformer.record(original)
                if not equivalent(original, output):
                    raise ValueError(f'Unexpected XML difference at record {index} ({local(original.tag)}).')
                if index % 100_000 == 0:
                    print(f'Checked {index:,} records', file=sys.stderr, flush=True)
            return transformer.index.summary()
        finally:
            db.close()


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('source', type=Path)
    cli.add_argument('output', type=Path)
    cli.add_argument('--key-file', required=True, type=Path, help='Private 32-byte key, created on first use.')
    cli.add_argument('--config', type=Path, help='JSON dictionary for the output language and public hosts.')
    cli.add_argument('--coordinates', action='store_true', help='Mask geographic coordinates when present.')
    cli.add_argument('--verify', action='store_true', help='Compare an existing output against the input and key.')
    args = cli.parse_args()
    try:
        paths = (args.source, args.output, args.key_file) + ((args.config,) if args.config else ())
        if len({item.resolve() for item in paths}) != len(paths) or any(
            a.exists() and b.exists() and a.samefile(b)
            for index, a in enumerate(paths) for b in paths[index + 1:]
        ):
            raise ValueError('Input, output and key must be different files.')
        cfg = configuration(args.config)
        catalog = ModelCatalog.scan(args.source)
        engine = Transformer(select_key(args.key_file, create=not args.verify), args.coordinates, catalog, cfg)
        if args.verify:
            verification = verify(args.source, args.output, engine)
        else:
            stage = args.output.with_name(args.output.name + '.' + secrets.token_hex(8) + '.part')
            try:
                transform(args.source, stage, engine)
                os.replace(stage, args.output)
            finally:
                stage.unlink(missing_ok=True)
            verification = {}
        print(json.dumps({
            'classes': len(engine.classes), 'records': sum(engine.classes.values()), 'language': cfg['language'],
            **dict(sorted(engine.stats.items())), **verification,
        }, ensure_ascii=False, indent=2))
    except (ValueError, OSError, etree.LxmlError, sqlite3.Error, BadZipFile) as exc:
        cli.exit(1, f'{exc}\n')


if __name__ == '__main__':
    main()
