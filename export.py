#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
gcexport.py
"""

from datetime import datetime, timedelta, tzinfo
from getpass import getpass
from math import floor
from platform import python_version
from subprocess import call
from timeit import default_timer as timer

import argparse
import csv
import io
import json
import logging
import os
import os.path
import re
import string
import sys
import unicodedata
import zipfile

import http.cookiejar
import urllib.error
import urllib.parse
import urllib.request
import urllib

from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import Request

from filtering import update_download_stats, read_exclude


COOKIE_JAR = http.cookiejar.CookieJar()
OPENER = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(COOKIE_JAR), urllib.request.HTTPSHandler(debuglevel=0))

SCRIPT_VERSION = '1.0.0'

# it's almost the datetime format that is used by Garmin in the activity-search-service
ALMOST_RFC_1123 = "%a, %d %b %Y %H:%M" # JSON display fields -  Garmin didn't zero-pad the date and the hour, but %d and %H do

VALID_FILENAME_CHARS = f"-_.() {string.ascii_letters}{string.digits}"

# mapping of numeric parentTypeId to names in CSV output
PARENT_TYPE_ID = {
    1: 'running',
    2: 'cycling',
    3: 'hiking',
    4: 'other',
    9: 'walking',
    17: 'any',
    26: 'swimming',
    29: 'fitness_equipment',
    71: 'motorcycling',
    83: 'transition',
    144: 'diving',
    149: 'yoga',
    165: 'winter_sports'
}

# which typeId value should use pace instead of speed
USES_PACE = {1, 3, 9, 26} # running, hiking, walking, swimming

HR_ZONES_EMPTY = [None]*5

# max number of a ctivities that can be requested at once - but the limit is not known. 1000 should work
LIMIT_MAXIMUM = 1000

MAX_TRIES = 3

CSV_TEMPLATE = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'csv_header_default.properties')

WEBHOST = 'https://connect.garmin.com'
REDIRECT = 'https://connect.garmin.com/modern/'
BASE_URL = 'https://connect.garmin.com/en-US/signin'
SSO = 'https://sso.garmin.com/sso'
CSS = 'https://static.garmincdn.com/com.garmin.connect/ui/css/gauth-custom-v1.2-min.css'

DATA = {
    'service': REDIRECT,
    'webhost': WEBHOST,
    'source': BASE_URL,
    'redirectAfterAccountLoginUrl': REDIRECT,
    'redirectAfterAccountCretionUrl': REDIRECT,
    'gauthHost': SSO,
    'locale': 'en-US',
    'id': 'gauth-widget',
    'cssUrl': CSS,
    'clientId': 'GarminConnect',
    'rememberMeShown': 'true',
    'rememberMeChecked': 'false',
    'createAccountShown': 'true',
    'openCreateAccount': 'false',
    'displayNameShown': 'false',
    'consumeServiceTicket': 'false',
    'initialFocus': 'true',
    'embedWidget': 'false',
    'generateExtraServiceTicket': 'true',
    'generateTwoExtraServiceTickets': 'false',
    'generateNoServiceticket': 'false',
    'globalOptInShown': 'true',
    'globalOptInChecked': 'false',
    'mobile': 'false',
    'connectLegalTerms': 'true',
    'locationPromptShown': 'true',
    'showPassword': 'true'
}

#URLs for various services

URL_GC_LOGIN = 'https://sso.garmin.com/sso/signin?' + urlencode(DATA)
URL_GC_POST_AUTH = 'https://connect.garmin.com/modern/activities?'
URL_GC_PROFILE = 'https://connect.garmin.com/modern/profile'
URL_GC_USERSTATS = 'https://connect.garmin.com/modern/proxy/userstats-service/statistics/'
URL_GC_LIST = 'https://connect.garmin.com/modern/proxy/activitylist-service/activities/search/activities?'
URL_GC_ACTIVITY = 'https://connect.garmin.com/modern/proxy/activity-service/activity/'
URL_GC_DEVICE = 'https://connect.garmin.com/modern/proxy/device-service/deviceservice/app-info/'
URL_GC_GEAR = 'https://connect.garmin.com/modern/proxy/gear-service/gear/filterGear?activityId='
URL_GC_ACT_PROPS = 'https://connect.garmin.com/modern/main/js/properties/activity_types/activity_types.properties'
URL_GC_EVT_PROPS = 'https://connect.garmin.com/modern/main/js/properties/event_types/event_types.properties'
URL_GC_GPX_ACTIVITY = 'https://connect.garmin.com/modern/proxy/download-service/export/gpx/activity/'
URL_GC_TCX_ACTIVITY = 'https://connect.garmin.com/modern/proxy/download-service/export/tcx/activity/'
URL_GC_ORIGINAL_ACTIVITY = 'http://connect.garmin.com/proxy/download-service/files/activity/'


def resolve_path(directory, subdir, time):
    """
    Replace time variables and returns changed path. Supported placeholders are {YYYY} and {MM}.

    :param directory: export root directory
    :param subdir: subdirectory that can have placeholders
    :param time: date-time-string
    :return: updated dictionary string
    """

    ret = os.path.join(directory, subdir)
    if re.compile(".*{YYYY}.*").match(ret):
        ret = ret.replace("{YYYY}", time[0:4])
    if re.compile(".*{MM}.*").match(ret):
        ret = ret.replace("{MM}", time[5:7])

    return ret


def hhmmss_from_seconds(sec):
    """
    Converting seconds to HH:MM:SS time format.
    """

    if isinstance(sec, (float, int)):
        formatted_time = str(timedelta(seconds=int(sec))).zfill(8)
    else:
        formatted_time = '0.000'
    return formatted_time


def kmh_from_mps(mps):
    """
    Converting meters per second (mps) to km/h.
    """
    return str(mps * 3.6)


def sanitize_filename(name, max_length=0):
    """
    Removing or replacing characters that are unsafe for filename.
    """

    cleaned_filename = unicodedata.normalize('NKFD', name) if name else ''
    stripped_filename = ''.join(c for c in cleaned_filename if c in VALID_FILENAME_CHARS).replace(' ', '_')
    return stripped_filename[:max_length] if max_length > 0 else stripped_filename


def write_to_file(filename, content, mode='w', file_time=None):
    """
    description

    :param filename:
    """
    if mode =='w':
        write_file = io.open(filename, mode, encoding='utf-8')
        if isinstance(content, bytes):
            content = content.decode('utf-8')
    elif mode == 'wb':
        write_file = io.open(filename, mode)
    else:
        raise Exception('Unsupported file mode: ', mode)
    write_file.write(content)
    write_file.close()
    if file_time:
        os.utime(filename, (file_time, file_time))


def http_req(url, post=None, headers=None):
    """
    Making HTTP requests.
    :param url: URL for the request
    :param post: dictionary of POST
    """
    request = Request(url)

    # supported browsers
    request.add_header('User-Agent', 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/54.0.2816.0 Safari/537.36')
    request.add_header('nk', 'NT') # necessary to avoid HTTP error code 402
    if headers:
        for header_key, header_value in headers.items():
            request.add_header(header_key, header_value)
    if post:
        post = urlencode(post) # convert dictionary to POST parameter string.
        post = post.encode('utf-8')
    start_time = timer()
    try:
        response = OPENER.open(request, data=post)
    except HTTPError as ex:
        if hasattr(ex, 'code'):
            logging.error(f"Server couldn't fulfill the request, code {ex.code}, error {ex}")
            logging.info(f'Headers returned: \n{ex.info()}')
            raise
        else:
            raise
    except URLError as ex:
        if hasattr(ex, 'reason'):
            logging.error(f'Failed to reach url {url}, error: {ex}')
            raise
        else:
            raise
    logging.debug(f'Got {response.getcode()} in {timer()-start_time} s from {url}')
    logging.debug(f'Headers returned: \n{response.info()}')

    if response.getcode() == 204:
        # 204 = no content, e.g. for activities without GPS coordinates there is no GPX download.
        # Write an empty file to prevent redownloading it.
        logging.info(f'Got 204 for {url}, returning empty response')
        return b''
    elif response.getcode() != 200:
        raise Exception(f'Bad return code ({response.getcode()}) for: {url}')

    return response.read()


def http_req_as_string(url, post=None, headers=None):
    """
    Making HTTP requests, returning a string instead of bytes.
    """
    return http_req(url, post, headers).decode()


def load_properties(multiline, separator='=', comment_char='#', keys=None):
    """
    description
    """
