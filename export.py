#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
export.py
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
    'redirectAfterAccountCreationUrl': REDIRECT,
    'gauthHost': SSO,
    'locale': 'en_US',
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

# URLs for various services

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
    :param directory:   export root directory
    :param subdir:      subdirectory that can have placeholders
    :param time:        date-time-string
    :return:            updated dictionary string
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
    Helper function that perssts content to a file.
    :param filename:        name of the file to write
    :param content:         content to write; can be 'bytes' or 'str'
                            If it is 'bytes' and the mode 'w', it will be converted/decoded.
    :param mode:            'w' or 'wb'
    :param file_time:       if given use as timestamp for the file written (in seconds since 1970-01-01)
    """
    if mode == 'w':
        write_file = io.open(filename, mode, encoding='utf-8')
        if isinstance(content, bytes):
            content = content.decode('utf-8')
    elif mode == 'wb':
        write_file = io.open(filename, mode, encoding="utf-8")
    else:
        raise Exception('Unsupported file mode: ', mode)
    write_file.write(content)
    write_file.close()
    if file_time:
        os.utime(filename, (file_time, file_time))


def http_req(url, post=None, headers=None):
    """
    Making HTTP requests.
    :param url:     URL for the request
    :param post:    dictionary of POST
    :param headers: dictionary of headers
    :return:        response body (type 'bytes')
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
            logging.error("Server couldn't fulfill the request, code %s, error: %s", ex.code, ex)
            logging.info('Headers returned:\n%s', ex.info())
            raise
    except URLError as ex:
        if hasattr(ex, 'reason'):
            logging.error('Failed to reach url %s, error: %s', url, ex)
            raise
    logging.debug('Got %s in %s s from %s', response.getcode(), timer() - start_time, url)
    logging.debug('Headers returned: \n%s', response.info())

    if response.getcode() == 204:
        # 204 = no content, e.g. for activities without GPS coordinates there is no GPX download.
        # Write an empty file to prevent redownloading it.
        logging.info('Got 204 for %s, returning empty response', url)
        return b''
    if response.getcode() != 200:
        raise Exception(f'Bad return code ({response.getcode()}) for: {url}')

    return response.read()


def http_req_as_string(url, post=None, headers=None):
    """
    Making HTTP requests, returning a string instead of bytes.
    """
    return http_req(url, post, headers).decode()


def load_properties(multiline, separator='=', comment_char='#', keys=None):
    """
    Reading multiline string of properties (key-value pair separated by *separator*) into a dict.

    :param multiline:       input string of properties
    :param separator:       separator between key and value
    :param comment_char:    lines starting with this char are considered as comments, not key-value pairs
    :param keys:            list to append the keys to
    :return:
    """
    properties = {}
    for line in multiline.splitlines():
        stripped_line = line.strip()
        if stripped_line and not stripped_line.startswith(comment_char):
            key_value = stripped_line.split(separator)
            key = key_value[0].strip()
            value = separator.join(key_value[1:]).strip().strip('"')
            properties[key] = value
            if keys is not None:
                keys.append(key)
    return properties


def value_if_found_else_key(some_dict, key):
    """
    Lookup a value in some_dict and use the key itself as a fallback.
    """
    return some_dict.get(key, key)


def present(element, act):
    """
    Returning True if act[element] is valid and not None.
    """
    if not act and element not in act:
        return False
    return act[element]


def absent_or_null(element, act):
    """
    Return False only if act[element] is valid and not None.
    """
    if not act and element not in act:
        return True
    if act[element]:
        return False
    return True


def from_activities_or_details(element, act, detail, detail_container):
    """
    Return detail[detail_container][element] if valid and act[element] (or None) otherwise.
    """
    if absent_or_null(detail_container, detail) or absent_or_null(element, detail[detail_container]):
        return None if absent_or_null(element, act) else act[element]
    return detail[detail_container][element]


def trunc6(some_float):
    """
    Return the given float as a string formatted with six digit precision.
    """
    return "{0:12.6f}".format(floor(some_float * 1000000) / 1000000).lstrip()


class FixedOffset(tzinfo):
    """
    Fixed offset in minutes east from UTC.
    """

    def __init__(self, offset, name):
        super().__init__()
        self.__offset = timedelta(minutes=offset)
        self.__name = name


    def utc_offset(self, dt):
        return self.__offset

    def tzname(self, dt):
        return self.__name

    def dst(self, dt):
        return timedelta(0)


def offset_date_time(time_local, time_gmt):
    """
    Building an 'aware' datetime from two naive datetime objects (that is timestamps as present in the activitylist-service.json), using the time difference as offset.
    """
    local_dt = datetime_from_iso(time_local)
    gmt_dt = datetime_from_iso(time_gmt)
    offset = local_dt - gmt_dt
    offset_tz = FixedOffset(offset.seconds // 60, "LCL")
    return local_dt.replace(tzinfo=offset_tz)

def datetime_from_iso(iso_date_time):
    """
    Calling 'datetime.strptime' supporting different ISO time formats
    (with or without 'T' between date and time, with or without microseconds, but without offset).
    :param iso_date_time:   timestamp string in ISO format
    :return:                a 'naive' datetime
    """
    pattern = re.compile(r"(\d{4}-\d{2}-\d{2})[T ](\d{2}:\d{2}:\d{2})(\.\d+)?")
    match = pattern.match(iso_date_time)
    if not match:
        raise Exception(f'Invalid ISO timestamp {iso_date_time}.')
    micros = match.group(3) if match.group(3) else ".0"
    iso_with_micros = f'{match.group(1)} {match.group(2)}{micros}'
    return datetime.strptime(iso_with_micros, "%Y-%m-%d %H:%M:%S.%f")


def epoch_seconds_from_summary(summary):
    """
    Function determining the start time in epoch seconds (seconds since 1970-01-01).
    :param summary:     summary dict
    :return:            epoch seconds as integer
    """
    if present('beginTimestamp', summary):
        return summary['beginTimestamp'] // 1000
    if present('startTimeLocal', summary) and present('startTimeGMT', summary):
        dt = offset_date_time(summary['startTimeLocal'], summary['startTimeGMT'])
        return int(dt.timestamp())
    logging.info('No timestamp found in activity %s', summary['activityId'])
    return None


def pace_or_speed_raw(type_id, parent_type_id, mps):
    """
    Convert speed (m/s) to speed (km/h) or pace (min/km) depending on type and parent type.         
    """
    kmh = 3.6 * mps
    if (type_id in USES_PACE) or (parent_type_id in USES_PACE):
        return 60/kmh
    return kmh


def pace_or_speed_formatted(type_id, parent_type_id, mps):
    """
    Convert speed (m/s) to string: speed (km/h as x.x) or pace (min/km as MM:SS),
    depending on type and parent type.
    """
    kmh = 3.6 * mps
    if (type_id in USES_PACE) or (parent_type_id in USES_PACE):
        return '{0:02d}:{1:02d}'.format(*divmod(int(round(3600/kmh)), 60))
    return "{0:.1f}".format(round(kmh, 1))


class CsvFilter:
    """
    Collects, filters and writes CSV files.
    """

    def __init__(self, csv_file, csv_header_properties):
        self.__csv_file = csv_file
        with open(csv_header_properties, 'r', encoding="utf-8") as properties:
            csv_header_properties = properties.read()
        self.__csv_columns = []
        self.__csv_headers = load_properties(csv_header_properties, keys=self.__csv_columns)
        self.__csv_field_names = []
        for column in self.__csv_columns:
            self.__csv_field_names.append(self.__csv_headers[column])
        self.__writer = csv.DictWriter(self.__csv_file, fieldnames=self.__csv_field_names, quoting=csv.QUOTE_ALL)
        self.__current_row = {}

    def write_header(self):
        """
        Writing the active column names as CSV headers.
        """
        self.__writer.writeheader()

    def write_row(self):
        """
        Writing the prepared CSV record.
        """
        self.__writer.writerow(self.__current_row)
        self.__current_row = {}

    def set_column(self, name, value):
        """
        Storing a column value (if the column is active) into the record prepared for the next write_row call
        """
        if value and name in self.__csv_columns:
            self.__current_row[self.__csv_headers[name]] = value

    def is_column_active(self, name):
        """
        Return True if the column is present in the header template.
        """
        return name in self.__csv_columns

def parse_arguments(argv):
    """
    Setup the argument parser and parse the command line arguments.
    """
    current_date = datetime.now().strftime('%Y-%m-%d')
    activities_directory = f'./{current_date}_garmin_connect_export'

    parser = argparse.ArgumentParser(description='Garmin Connect Exporter')

    parser.add_argument('-v','--version', action='version', version='%(prog)s ' + SCRIPT_VERSION,
                        help='print version and exit')
    parser.add_argument('-vv', '--verbose', action='count', default=0,
                        help='show output and log verbosity, save more intermediate files')
    parser.add_argument('-u', '--username',
                        help='Garmin Connect username or email address')
    parser.add_argument('-p', '--password',
                        help='Garmin Connect password')
    parser.add_argument('-c', '--count', default='1',
                        help='number of recent activities to download, or \'all\' (default: 1)')
    parser.add_argument('-e', '--external',
                        help='path to external program to pass CSV file too')
    parser.add_argument('-a', '--args',
                        help='additional arguments to pass to external program')
    parser.add_argument('-f', '--format', choices=['gpx', 'tcx', 'original', 'json'], default='gpx',
                        help="export format; can be 'gpx', 'tcx', 'original' or 'json' (default: 'gpx')")
    parser.add_argument('-d', '--directory', default=activities_directory,
                        help='the directory to export to (default: \'./YYYY-MM-DD_garmin_connect_export\')')
    parser.add_argument('-s', '--subdir',
                        help='the subdirectory for activity files (tcx, gpx etc.), supported placeholders are {YYYY} and {MM} (default: export directory)')
    parser.add_argument('-lp', '--logpath',
                        help='the directory to store logfiles (default: same as for --directory)')
    parser.add_argument('-u', '--unzip', action='store_true',
                        help='if downloading ZIP files (format: \'original\'), unzip the file and remove the ZIP file')
    parser.add_argument('-ot', '--originaltime', action='store_true',
                        help='will set downloaded (and possibly unzipped) file time to the activity start time')
    parser.add_argument('--desc', type=int, nargs='?', const=0, default=None,
                        help='append the activity\'s description to the file name of the download; limit size if number is given')
    parser.add_argument('-t', '--template', default=CSV_TEMPLATE,
                        help='template file with desired columns for CSV output')
    parser.add_argument('-fp', '--fileprefix', action='count', default=0,
                        help='set the local time as activity file name prefix')
    parser.add_argument('-sa', '--start_activity_no', type=int, default=1,
                        help='give index for first activity to import, i.e. skipping the newest activities')
    parser.add_argument('-ex', '--exclude', metavar='FILE',
                        help='JSON file with Array of activity IDs to exclude from download. Format example: {"ids": ["6176888711"]}')

    return parser.parse_args(argv[1:])

def login_to_garmin_connect(args):
    """
    Perform all HTTP requests to login to Garmin Connect.
    """
    username = args.username if args.username else input('Username: ')
    password = args.password if args.password else getpass()

    logging.debug('Login params: %s', urlencode(DATA))

    # Initially, to get a valid session cookie it is necessary to pull the login page.
    print('Connecting to Garmin Connect...', end='')
    logging.info('Connecting to %s', URL_GC_LOGIN)
    connect_response = http_req_as_string(URL_GC_LOGIN)
    if args.verbosity > 0:
        write_to_file(os.path.join(args.directory, 'connect_response.html'), connect_response, 'w')
    for cookie in COOKIE_JAR:
        logging.debug('Cookie %s: %s', cookie.name, cookie.value)
    print('Done')

    # Actual login - fields that are passed in a typical Garmin login.
    post_data = {
        'username': username,
        'password': password,
        'embed': 'false',
        'rememberme': 'on'
    }

    headers = {
        'referer': URL_GC_LOGIN
    }

    print('Requesting Login ticket...', end='')
    logging.info('Requesting Login ticket')
    login_response = http_req_as_string(f'{URL_GC_LOGIN}#', post_data, headers)

    for cookie in COOKIE_JAR:
        logging.debug('Cookie %s: %s', cookie.name, cookie.value)
    if args.verbosity > 0:
        write_to_file(os.path.join(args.directory, 'login_response.html'), login_response, 'w')

    # extract the ticket from the login response
    pattern = re.compile(r".*\?ticket=([-\w]+)\";.*", re.MULTILINE | re.DOTALL)
    match = pattern.match(login_response)
    if not match:
        raise Exception('Could not find ticket in the login response. Cannot log in.')
    login_ticket = match.group(1)
    print('Done. Ticket=', login_ticket, sep='')

    print('Authenticating...', end='')
    logging.info('Authentication URL %s', f'{URL_GC_POST_AUTH}ticket={login_ticket}')
    http_req(f'{URL_GC_POST_AUTH}ticket={login_ticket}')
    print('Done')

def csv_write_record(csv_filter, extract, activity, details, activity_type_name, event_type_name):
    """
    Write out the given data as a CSV record.
    """
    type_id = 4 if absent_or_null('activityType', activity) else activity['activityType']['typeId']
    parent_type_id = 4 if absent_or_null('activityType', activity) else activity['activityType']['parentTypeId']
    if present(parent_type_id, PARENT_TYPE_ID):
        parent_type_key = PARENT_TYPE_ID[parent_type_id]
    else:
        parent_type_key = None
        logging.warning('Unknown parentType %s', str(parent_type_id))

    # get some values from details if present
    start_latitude = from_activities_or_details('startLatitude', activity, details, 'summaryDTO')
    start_longitude = from_activities_or_details('startLongitude', activity, details, 'summaryDTO')
    end_latitude = from_activities_or_details('endLatitude', activity, details, 'summaryDTO')
    end_longitude = from_activities_or_details('endLongitude', activity, details, 'summaryDTO')

    csv_filter.set_column('id', str(activity['activityId']))
    csv_filter.set_column('url', 'https://connect.garmin.com/modern/activity/' + str(activity['activityId']))
    csv_filter.set_column('activityName', activity['activityName'] if present('activityName', activity) else None)
    csv_filter.set_column('description', activity['description'] if present('description', activity) else None)
    csv_filter.set_column('startTimeIso', extract['start_time_with_offset'].isoformat())
    csv_filter.set_column('startTime1123', extract['start_time_with_offset'].strftime(ALMOST_RFC_1123))
    csv_filter.set_column('startTimeMillis', str(activity['beginTimestamp']) if present('beginTimestamp', activity) else None)
    csv_filter.set_column('startTimeRaw', details['summaryDTO']['startTimeLocal'] if present('startTimeLocal', details['summaryDTO']) else None)
    csv_filter.set_column('endTimeIso', extract['end_time_with_offset'].isoformat() if extract['end_time_with_offset'] else None)
    csv_filter.set_column('endTime1123', extract['end_time_with_offset'].strftime(ALMOST_RFC_1123) if extract['end_time_with_offset'] else None)
    csv_filter.set_column('endTimeMillis', str(activity['beginTimestamp'] + extract['elapsed_seconds'] * 1000) if present('beginTimestamp', activity) else None)
    csv_filter.set_column('durationRaw', str(round(activity['duration'], 3)) if present('duration', activity) else None)
    csv_filter.set_column('duration', hhmmss_from_seconds(round(activity['duration'])) if present('duration', activity) else None)
    csv_filter.set_column('elapsedDurationRaw', str(round(extract['elapsed_duration'], 3)) if extract['elapsed_duration'] else None)
    csv_filter.set_column('elapsedDuration', hhmmss_from_seconds(round(extract['elapsed_duration'])) if extract['elapsed_duration'] else None)
    csv_filter.set_column('movingDurationRaw', str(round(details['summaryDTO']['movingDuration'], 3)) if present('movingDuration', details['summaryDTO']) else None)
    csv_filter.set_column('movingDuration', hhmmss_from_seconds(round(details['summaryDTO']['movingDuration'])) if present('movingDuration', details['summaryDTO']) else None)
    csv_filter.set_column('distanceRaw', "{0:.5f}".format(activity['distance'] / 1000) if present('distance', activity) else None)
    csv_filter.set_column('averageSpeedRaw', kmh_from_mps(details['summaryDTO']['averageSpeed']) if present('averageSpeed', details['summaryDTO']) else None)
    csv_filter.set_column('averageSpeedPaceRaw', trunc6(pace_or_speed_raw(type_id, parent_type_id, activity['averageSpeed'])) if present('averageSpeed', activity) else None)
    csv_filter.set_column('averageSpeedPace', pace_or_speed_formatted(type_id, parent_type_id, activity['averageSpeed']) if present('averageSpeed', activity) else None)
    csv_filter.set_column('averageMovingSpeedRaw', kmh_from_mps(details['summaryDTO']['averageMovingSpeed']) if present('averageMovingSpeed', details['summaryDTO']) else None)
    csv_filter.set_column('averageMovingSpeedPaceRaw', trunc6(pace_or_speed_raw(type_id, parent_type_id, details['summaryDTO']['averageMovingSpeed'])) if present('averageMovingSpeed', details['summaryDTO']) else None)
    csv_filter.set_column('averageMovingSpeedPace', pace_or_speed_formatted(type_id, parent_type_id, details['summaryDTO']['averageMovingSpeed']) if present('averageMovingSpeed', details['summaryDTO']) else None)
    csv_filter.set_column('maxSpeedRaw', kmh_from_mps(details['summaryDTO']['maxSpeed']) if present('maxSpeed', details['summaryDTO']) else None)
    csv_filter.set_column('maxSpeedPaceRaw', trunc6(pace_or_speed_raw(type_id, parent_type_id, details['summaryDTO']['maxSpeed'])) if present('maxSpeed', details['summaryDTO']) else None)
    csv_filter.set_column('maxSpeedPace', pace_or_speed_formatted(type_id, parent_type_id, details['summaryDTO']['maxSpeed']) if present('maxSpeed', details['summaryDTO']) else None)
    csv_filter.set_column('elevationLoss', str(round(details['summaryDTO']['elevationLoss'], 2)) if present('elevationLoss', details['summaryDTO']) else None)
    csv_filter.set_column('elevationLossUncorr', str(round(details['summaryDTO']['elevationLoss'], 2)) if not activity['elevationCorrected'] and present('elevationLoss', details['summaryDTO']) else None)
    csv_filter.set_column('elevationLossCorr', str(round(details['summaryDTO']['elevationLoss'], 2)) if activity['elevationCorrected'] and present('elevationLoss', details['summaryDTO']) else None)
    csv_filter.set_column('elevationGain', str(round(details['summaryDTO']['elevationGain'], 2)) if present('elevationGain', details['summaryDTO']) else None)
    csv_filter.set_column('elevationGainUncorr', str(round(details['summaryDTO']['elevationGain'], 2)) if not activity['elevationCorrected'] and present('elevationGain', details['summaryDTO']) else None)
    csv_filter.set_column('elevationGainCorr', str(round(details['summaryDTO']['elevationGain'], 2)) if activity['elevationCorrected'] and present('elevationGain', details['summaryDTO']) else None)
    csv_filter.set_column('minElevation', str(round(details['summaryDTO']['minElevation'], 2)) if present('minElevation', details['summaryDTO']) else None)
    csv_filter.set_column('minElevationUncorr', str(round(details['summaryDTO']['minElevation'], 2)) if not activity['elevationCorrected'] and present('minElevation', details['summaryDTO']) else None)
    csv_filter.set_column('minElevationCorr', str(round(details['summaryDTO']['minElevation'], 2)) if activity['elevationCorrected'] and present('minElevation', details['summaryDTO']) else None)
    csv_filter.set_column('maxElevation', str(round(details['summaryDTO']['maxElevation'], 2)) if present('maxElevation', details['summaryDTO']) else None)
    csv_filter.set_column('maxElevationUncorr', str(round(details['summaryDTO']['maxElevation'], 2)) if not activity['elevationCorrected'] and present('maxElevation', details['summaryDTO']) else None)
    csv_filter.set_column('maxElevationCorr', str(round(details['summaryDTO']['maxElevation'], 2)) if activity['elevationCorrected'] and present('maxElevation', details['summaryDTO']) else None)
    csv_filter.set_column('elevationCorrected', 'true' if activity['elevationCorrected'] else 'false')
    # csv_record += empty_record  # no minimum heart rate in JSON
    csv_filter.set_column('maxHRRaw', str(details['summaryDTO']['maxHR']) if present('maxHR', details['summaryDTO']) else None)
    csv_filter.set_column('maxHR', "{0:.0f}".format(activity['maxHR']) if present('maxHR', activity) else None)
    csv_filter.set_column('averageHRRaw', str(details['summaryDTO']['averageHR']) if present('averageHR', details['summaryDTO']) else None)
    csv_filter.set_column('averageHR', "{0:.0f}".format(activity['averageHR']) if present('averageHR', activity) else None)
    csv_filter.set_column('caloriesRaw', str(details['summaryDTO']['calories']) if present('calories', details['summaryDTO']) else None)
    csv_filter.set_column('calories', "{0:.0f}".format(details['summaryDTO']['calories']) if present('calories', details['summaryDTO']) else None)
    csv_filter.set_column('vo2max', str(activity['vO2MaxValue']) if present('vO2MaxValue', activity) else None)
    csv_filter.set_column('aerobicEffect', str(round(details['summaryDTO']['trainingEffect'], 2)) if present('trainingEffect', details['summaryDTO']) else None)
    csv_filter.set_column('anaerobicEffect', str(round(details['summaryDTO']['anaerobicTrainingEffect'], 2)) if present('anaerobicTrainingEffect', details['summaryDTO']) else None)
    csv_filter.set_column('hrZone1Low', str(extract['hrZones'][0]['zoneLowBoundary']) if present('zoneLowBoundary', extract['hrZones'][0]) else None)
    csv_filter.set_column('hrZone1Seconds', "{0:.0f}".format(extract['hrZones'][0]['secsInZone']) if present('secsInZone', extract['hrZones'][0]) else None)
    csv_filter.set_column('hrZone2Low', str(extract['hrZones'][1]['zoneLowBoundary']) if present('zoneLowBoundary', extract['hrZones'][1]) else None)
    csv_filter.set_column('hrZone2Seconds', "{0:.0f}".format(extract['hrZones'][1]['secsInZone']) if present('secsInZone', extract['hrZones'][1]) else None)
    csv_filter.set_column('hrZone3Low', str(extract['hrZones'][2]['zoneLowBoundary']) if present('zoneLowBoundary', extract['hrZones'][2]) else None)
    csv_filter.set_column('hrZone3Seconds', "{0:.0f}".format(extract['hrZones'][2]['secsInZone']) if present('secsInZone', extract['hrZones'][2]) else None)
    csv_filter.set_column('hrZone4Low', str(extract['hrZones'][3]['zoneLowBoundary']) if present('zoneLowBoundary', extract['hrZones'][3]) else None)
    csv_filter.set_column('hrZone4Seconds', "{0:.0f}".format(extract['hrZones'][3]['secsInZone']) if present('secsInZone', extract['hrZones'][3]) else None)
    csv_filter.set_column('hrZone5Low', str(extract['hrZones'][4]['zoneLowBoundary']) if present('zoneLowBoundary', extract['hrZones'][4]) else None)
    csv_filter.set_column('hrZone5Seconds', "{0:.0f}".format(extract['hrZones'][4]['secsInZone']) if present('secsInZone', extract['hrZones'][4]) else None)
    csv_filter.set_column('averageRunCadence', str(round(details['summaryDTO']['averageRunCadence'], 2)) if present('averageRunCadence', details['summaryDTO']) else None)
    csv_filter.set_column('maxRunCadence', str(details['summaryDTO']['maxRunCadence']) if present('maxRunCadence', details['summaryDTO']) else None)
    csv_filter.set_column('strideLength', str(round(details['summaryDTO']['strideLength'], 2)) if present('strideLength', details['summaryDTO']) else None)
    csv_filter.set_column('steps', str(activity['steps']) if present('steps', activity) else None)
    csv_filter.set_column('averageCadence', str(activity['averageBikingCadenceInRevPerMinute']) if present('averageBikingCadenceInRevPerMinute', activity) else None)
    csv_filter.set_column('maxCadence', str(activity['maxBikingCadenceInRevPerMinute']) if present('maxBikingCadenceInRevPerMinute', activity) else None)
    csv_filter.set_column('strokes', str(activity['strokes']) if present('strokes', activity) else None)
    csv_filter.set_column('averageTemperature', str(details['summaryDTO']['averageTemperature']) if present('averageTemperature', details['summaryDTO']) else None)
    csv_filter.set_column('minTemperature', str(details['summaryDTO']['minTemperature']) if present('minTemperature', details['summaryDTO']) else None)
    csv_filter.set_column('maxTemperature', str(details['summaryDTO']['maxTemperature']) if present('maxTemperature', details['summaryDTO']) else None)
    csv_filter.set_column('device', extract['device'] if extract['device'] else None)
    csv_filter.set_column('gear', extract['gear'] if extract['gear'] else None)
    csv_filter.set_column('activityTypeKey', activity['activityType']['typeKey'].title() if present('typeKey', activity['activityType']) else None)
    csv_filter.set_column('activityType', value_if_found_else_key(activity_type_name, 'activity_type_' + activity['activityType']['typeKey']) if present('activityType', activity) else None)
    csv_filter.set_column('activityParent', value_if_found_else_key(activity_type_name, 'activity_type_' + parent_type_key) if parent_type_key else None)
    csv_filter.set_column('eventTypeKey', activity['eventType']['typeKey'].title() if present('typeKey', activity['eventType']) else None)
    csv_filter.set_column('eventType', value_if_found_else_key(event_type_name, activity['eventType']['typeKey']) if present('eventType', activity) else None)
    csv_filter.set_column('privacy', details['accessControlRuleDTO']['typeKey'] if present('typeKey', details['accessControlRuleDTO']) else None)
    csv_filter.set_column('fileFormat', details['metadataDTO']['fileFormat']['formatKey'] if present('fileFormat', details['metadataDTO']) and present('formatKey', details['metadataDTO']['fileFormat']) else None)
    csv_filter.set_column('tz', details['timeZoneUnitDTO']['timeZone'] if present('timeZone', details['timeZoneUnitDTO']) else None)
    csv_filter.set_column('tzOffset', extract['start_time_with_offset'].isoformat()[-6:])
    csv_filter.set_column('locationName', details['locationName'] if present('locationName', details) else None)
    csv_filter.set_column('startLatitudeRaw', str(start_latitude) if start_latitude else None)
    csv_filter.set_column('startLatitude', trunc6(start_latitude) if start_latitude else None)
    csv_filter.set_column('startLongitudeRaw', str(start_longitude) if start_longitude else None)
    csv_filter.set_column('startLongitude', trunc6(start_longitude) if start_longitude else None)
    csv_filter.set_column('endLatitudeRaw', str(end_latitude) if end_latitude else None)
    csv_filter.set_column('endLatitude', trunc6(end_latitude) if end_latitude else None)
    csv_filter.set_column('endLongitudeRaw', str(end_longitude) if end_longitude else None)
    csv_filter.set_column('endLongitude', trunc6(end_longitude) if end_longitude else None)
    csv_filter.set_column('sampleCount', str(extract['samples']['metricsCount']) if present('metricsCount', extract['samples']) else None)

    csv_filter.write_row()


def extract_device(device_dict, details, start_time_seconds, args, http_caller, file_writer):
    """
    Function trying to get the device details (and cache them as they're used for multiple activities)

    :param device_dict:         cache (dict) of already known devices
    :param details:             dict with the details of an activity, should contain a device ID
    :param start_time_seconds:  if given use as timestamp for the file written (in seconds since 1970-01-01)
    :param args:                command-line arguments (for the file_writer callback)
    :param http_caller:         callback to perform the HTTP call for downloading the device details
    :param file_writer:         callback that saves the device details in a file
    :return: string with the device name
    """
    if not present('metadataDTO', details):
        logging.warning('No metadataDTO')
        return None

    metadata = details['metadataDTO']
    device_app_inst_id = metadata['deviceApplicationInstallationId'] if present('deviceApplicationInstallationId', metadata) else None
    if device_app_inst_id:
        if device_app_inst_id not in device_dict:
            # observations...
            # details['metadataDTO']['deviceMetaDataDTO']['deviceId'] == null -> device uknown
            # details['metadataDTO']['deviceMetaDataDTO']['deviceId'] == '0' -> device unknown
            # details['metadataDTO']['deviceMetaDataDTO']['deviceId'] == 'someid' -> device known
            device_dict[device_app_inst_id] = None
            device_meta = metadata['deviceMetaDataDTO'] if present('deviceMetaDataDTO', metadata) else None
            device_id = device_meta['deviceId'] if present('deviceId', device_meta) else None
            if 'deviceId' not in device_meta or device_id and device_id != '0':
                device_json = http_caller(URL_GC_DEVICE + str(device_app_inst_id))
                file_writer(os.path.join(args.directory, f'device_{device_app_inst_id}.json'), device_json, 'w', start_time_seconds)
                if not device_json:
                    logging.warning('Device details %s are empty', device_app_inst_id)
                    device_dict[device_app_inst_id] = 'device_id:' + str(device_app_inst_id)
                else:
                    device_details = json.loads(device_json)
                    if present('productDisplayName', device_details):
                        device_dict[device_app_inst_id] = device_details['productDisplayName'] + ' ' + device_details['versionString']
                    else:
                        logging.warning('Device details %s incomplete', device_app_inst_id)
        return device_dict[device_app_inst_id]
    return None


def load_zones(activity_id, start_time_seconds, args, http_caller, file_writer):
    """
    Get the heart rate zones.
    :param activity_id:         ID of the activity (as a string)
    :param start_time_seconds:  if given use as timestamp for the file written (in seconds since 1970-01-01)
    :param args:                command-line arguments (for the file_writer callback)
    :param http_caller:         callback to perform the HTTP call for downloading the device details
    :param file_writer:         callback that saves the device details in a file
    :return: array with the heart rate zones
    """
    zones = HR_ZONES_EMPTY
    zones_json = http_caller(f'{URL_GC_ACTIVITY}{activity_id}/hrTimeInZones')
    file_writer(os.path.join(args.directory, f'activity_{activity_id}_zones.json'), zones_json, 'w', start_time_seconds)
    zones_raw = json.loads(zones_json)
    if not zones_raw:
        logging.warning(('HR zones %s are empty', activity_id))
    else:
        for raw_zone in zones_raw:
            if present('zoneNumber', raw_zone):
                index = raw_zone['zoneNumber'] - 1
                zones[index] = {}
                zones[index]['secsInZone'] = raw_zone['secsInZone']
                zones[index]['zoneLowBoundary'] = raw_zone['zoneLowBoundary']
    return zones


def load_gear(activity_id, args):
    """
    Retrieve the gear/equipment for an activity.
    """
    try:
        gear_json = http_req_as_string(URL_GC_GEAR + activity_id)
        gear = json.loads(gear_json)
        if gear:
            if args.verbosity > 0:
                write_to_file(os.path.join(args.directory, f'activity_{activity_id}-gear.json'), gear_json, 'w')
            gear_display_name = gear[0]['displayName'] if present('displayName', gear[0]) else None
            gear_model = gear[0]['customMakeModel'] if present('customMakeModel', gear[0]) else None
            logging.debug('Gear for %s = %s/%s', activity_id, gear_display_name, gear_model)
            return gear_display_name if gear_display_name else gear_model
        return None
    except HTTPError as e:
        logging.info('Unable to get gear for %d, error: %s', activity_id, e)


def export_data_file(activity_id, activity_details, args, file_time, append_desc, date_time):
    """
    Write the data of the activity to a file, depending on the chosen data format.
    The default filename is 'activity_' + activity_id, but this can be modified by the '--fileprefix' option
    and the 'appen_desc' parameter.
    The directory to write the file into can be modified by the '--subdir' option.
    :param activity_id:         ID of the activity (as string)
    :param activity_details:    details of the activity (for format 'json')
    :param args:                command-line arguments
    :param file_time:           if given the desired timestamp for the activity file (in seconds since 1970-01-01)
    :param append_desc:         suffix to the default filename
    :para date_time:            datetime in ISO format used for '--fileprefix' and '--subdir' options
    :return:                    True if the file was written, False if the file existed already
    """

    # time dependent subdirectory for activity  files, e.g. '{YYYY}'
    if not args.subdir is None:
        directory = resolve_path(args.directory, args.subdir, date_time)
    else:
        directory = args.directory

    if not os.path.isdir(directory):
        os.makedirs(directory)

    # timestamp as prefix for filename
    if args.fileprefix > 0:
        prefix = "{}-".format(date_time.replace("-", "").replace(":", "").replace(" ", "-"))
    else:
        prefix = ""

    original_basename = None
    if args.format == 'gpx':
        data_filename = os.path.join(directory, f'{prefix}activity_{activity_id}{append_desc}.gpx')
        download_url = f'{URL_GC_GPX_ACTIVITY}{activity_id}?full=true'
        file_mode = 'w'
    elif args.format == 'tcx':
        data_filename = os.path.join(directory, f'{prefix}activity_{activity_id}{append_desc}.tcx')
        download_url = f'{URL_GC_TCX_ACTIVITY}{activity_id}?full=true'
        file_mode = 'w'
    elif args.format == 'original':
        data_filename = os.path.join(directory, f'{prefix}activity_{activity_id}{append_desc}.zip')
        # but not all original files are in FIT format, some are gpx or TCX
        original_basename = os.path.join(directory, f'{prefix}activity_{activity_id}{append_desc}')
        download_url = URL_GC_ORIGINAL_ACTIVITY + activity_id
        file_mode = 'wb'
    elif args.format == 'json':
        data_filename = os.path.join(directory, f'{prefix}activity_{activity_id}{append_desc}.json')
        file_mode = 'w'
    else:
        raise Exception('Unrecognized format.')

    if os.path.isfile(data_filename):
        logging.debug('Data file for %s already exists', activity_id)
        print('\tData file already exists. Skipping...')
        return False

    if args.format == 'original' and (os.path.isfile(original_basename + '.fit') or os.path.isfile(original_basename + '.gpx') or os.path.isfile(original_basename + '.tcx')):
        logging.debug('Original data file for %s already exists', activity_id)
        print('\tOriginal data file already exists. Skipping...')
        return False

    if args.format != 'json':
        try:
            data = http_req(download_url)
        except HTTPError as e:
            if e.code == 500 and args.format == '.tcx':
                logging.info('Writing empty file since Garmin did not generate a TCX file for this activity...')
                data = ''
            else:
                logging.info('Got %s for %s', e.code, download_url)
                raise Exception(f'Failed. Got an HTTP error {e.code} for {download_url}')
    else:
        data = activity_details

    # persist file
    write_to_file(data_filename, data, file_mode, file_time)

    # Success: Add activity ID to downloaded_ids.json
    update_download_stats(activity_id, args.directory)

    if args.format == 'original':
        # even
        if args.unzip and data_filename[-3:].lower() == 'zip':
            logging.debug('Unzipping and removing original file, size is %s', os.stat(data_filename).st_size)
            if os.stat(data_filename).st_size > 0:
                zip_file = open(data_filename, 'rb')
                zip_obj = zipfile.ZipFile(zip_file)
                for name in zip_obj.namelist():
                    unzipped_name = zip_obj.extract(name, directory)
                    name_base, name_ext = os.path.splitext(name)
                    # handle some cases from 2020 activities, where Garmin added '_ACTIVITY' to the name in the ZIP and remove it
                    name_base = name_base.replace('_ACTIVITY', '')
                    new_name = os.path.join(directory, f'{prefix}activity_{name_base}{append_desc}{name_ext}')
                    logging.debug('renaming %s to %s', unzipped_name, new_name)
                    os.rename(unzipped_name, new_name)
                    if file_time:
                        os.utime(new_name, (file_time, file_time))
                zip_file.close()
            else:
                print('\tSkipping 0Kb zip file.')
            os.remove(data_filename)

    return True


def setup_logging(args):
    """
    Setup logging.
    """
    logpath = args.logpath if args.logpath else args.directory
    if not os.path.isdir(logpath):
        os.makedirs(logpath)

    logging.basicConfig(
        filename = os.path.join(logpath, 'gcexport.log'),
        level = logging.DEBUG,
        format = '%(asctime)s [%(levelname)-7.7s] %(message)s'
    )

    # set up logging to console
    console = logging.StreamHandler()
    console.setLevel(logging.WARN)
    formatter = logging.Formatter('[%(levelname)s] %(message)s')
    console.setFormatter(formatter)
    logging.getLogger('').addHandler(console)


def logging_verbosity(verbosity):
    """
    Adapt logging verbosity, separately for loglife and console output.
    """
    logger = logging.getLogger()
    for handler in logger.handlers:
        if isinstance(handler, logging.FileHandler):
            level = logging.DEBUG if verbosity > 0 else logging.INFO
            handler.setLevel(level)
            logging.info('New logfile level: %s', logging.getLevelName(level))
        elif isinstance(handler, logging.StreamHandler):
            level = logging.DEBUG if verbosity > 1 else (logging.INFO if verbosity > 0 else logging.WARN)
            handler.setLevel(level)
            logging.debug('New console log level: %s', logging.getLevelName(level))


def fetch_userstats(args):
    """
    HTTP request for getting user statistic like total number of activities. The JSON will be saved as a file 'userstats.json'.
    :param args:        command-line arguments (for args.directory, etc)
    :return:            JSON with user statistics
    """
    print('Getting display name...', end='')
    logging.info('Profile page %s', URL_GC_PROFILE)
    profile_page = http_req_as_string(URL_GC_PROFILE)
    if args.verbosity > 0:
        write_to_file(os.path.join(args.directory, 'profile.html'), profile_page, 'w')

    display_name = extract_display_name(profile_page)
    print('Done. displayName = ', display_name, sep='')

    print('Fetching user stats...', end='')
    logging.info('Userstats page %s', URL_GC_USERSTATS + display_name)
    result = http_req_as_string(URL_GC_USERSTATS + display_name)
    print('Done')

    write_to_file(os.path.join(args.directory, 'userstats.json'), result, 'w')

    return json.loads(result)


def extract_display_name(profile_page):
    """
    Extract the display name from the profile page HTML document.

    :param profile_page:        HTML document
    :return:                    the display name
    """
    # display name should be in the HTML document as "displayName": "John/Doe"
    pattern = re.compile(r".*\"displayName\":\"(.+?)\".*", re.MULTILINE | re.DOTALL)
    match = pattern.match(profile_page)
    if not match:
        raise Exception('Did not find the display name in the profile page.')
    display_name = match.group(1)
    return display_name


def fetch_activity_list(args, total_to_download):
    """
    Fetch the first 'total_to_download' activity summaries; as a side effect save them in .JSON format.
    :param args:                command-line arguments (for args.directory, etc.)
    :param total_to_download:   number of activities to download
    :return:                    list of activity summaries
    """
    activities = []

    total_downloaded = 0
    while total_downloaded < total_to_download:
        if total_to_download - total_downloaded > LIMIT_MAXIMUM:
            num_to_download = LIMIT_MAXIMUM
        else:
            num_to_download = total_to_download - total_downloaded

        chunk = fetch_activity_chunk(args, num_to_download, total_downloaded)
        activities.extend(chunk)
        total_downloaded += num_to_download

    # it seems that parent multisport activities are not counted in userstats
    if len(activities) != total_to_download:
        logging.info('Expected %s activities, got %s', total_to_download, len(activities))
    return activities


def annotate_activity_list(activities, start, exclude_list):
    """
    Annotate activity list.
    """
    action_list = []
    for index, a in enumerate(activities):
        if index < (start - 1):
            action = 's'
        elif str(a['activityId']) in exclude_list:
            action = 'e'
        else:
            action = 'd'

        action_list.append(dict(index=index, action=action, activity=a))

    return action_list


def fetch_activity_chunk(args, num_to_download, total_downloaded):
    """
    Fetch a chunk of activity summaries. As a side effect save them in the JSON format.
    :param args:                command-line ar guments (for args.directory, etc.)
    :param num_to_download:     number of summaries to wodnload in this chunk
    :param total_downloaded:    number of already downloaded summaries in previous chunks
    :return:                    List of activity summaries
    """

    search_parameters = {
        'start': total_downloaded,
        'limit': num_to_download
    }
    print('Querying list of activities ', total_downloaded+1, '..', total_downloaded+num_to_download, '...', sep='', end='')
    logging.info('Activity list URL %s', URL_GC_LIST + urlencode(search_parameters))
    result = http_req_as_string(URL_GC_LIST + urlencode(search_parameters))
    print('Done.')

    # persist JSON activities list
    current_index = total_downloaded + 1
    activities_list_filename = f'activities-{current_index}-{total_downloaded+num_to_download}.json'
    write_to_file(os.path.join(args.directory, activities_list_filename), result, 'w')
    activity_summaries = json.loads(result)
    fetch_multisports(activity_summaries, http_req_as_string, args)
    return activity_summaries


def fetch_multisports(activity_summaries, http_caller, args):
    """
    Search 'activity_summaries' for multisport activities and then fetch the information for the activity parts
    and insert them into the 'activity_summaries' just after the multisport activity.
    :param activity_summaries:  list of activity_summaries, will be modified in-place
    :param http_caller:         callback to perform the HTTP call for downloading the activity details
    :param args:                command-line arguments (for args.directory, etc.)
    """
    for idx, child_summary in enumerate(activity_summaries):
        type_key = None if absent_or_null('activityType', child_summary) else child_summary['activityType']['typeKey']
        if type_key == 'multi_sport':
            details_string, details = fetch_details(child_summary['activityId'], http_caller)

            child_ids = details['metadataDTO']['childIds'] if 'metadataDTO' in details and 'childIds' in details['metadataDTO'] else None
            # inserting the childs in reversed order always at the same index to get
            for child_id in reversed(child_ids):
                child_string, child_details = fetch_details(child_id, http_caller)
                if args.verbosity > 0:
                    write_to_file(os.path.join(args.directory, f'child_{child_id}.json'), child_string, 'w')
                child_summary = dict()
                copy_details_to_summary(child_summary, child_details)
                activity_summaries.insert(idx + 1, child_summary)

def fetch_details(activity_id, http_caller):
    """
    Try to get the activity details for an activity.
    :param activity_id:     id of the activity to fetch
    :param http_caller:     callback to perform the HTTP call for downloading the activity details
    :return details_as_string, details_as_json_dict:
    """
    activity_details = None
    details = None
    tries = MAX_TRIES
    while tries > 0:
        activity_details = http_caller(f'{URL_GC_ACTIVITY}{activity_id}')
        details = json.loads(activity_details)
        if details['summaryDTO']:
            tries = 0
        else:
            logging.info('Retrying activity details download %s', URL_GC_ACTIVITY + str(activity_id))
            tries -= 1
            if tries == 0:
                raise Exception(f"Didn't get 'summaryDTO' after {MAX_TRIES} tries for {activity_id}.")
        return activity_details, details


def copy_details_to_summary(summary, details):
    """
    Add some activity properties from the 'details' dict to the 'summary' dict. The choice of which properties are copied is determined
    by the properties used by the 'csv_write_second' method.
    :param summary: summary dict, will be modified in-place
    :param details: details dict
    """
    summary['activityId'] = details['activityId']
    summary['activityName'] = details['activityName']
    summary['description'] = details['description'] if present('description', details) else None
    summary['activityType'] = {}
    summary['activityType']['typeId'] = details['activityTypeDTO']['typeId'] if 'activityTypeDTO' in details and present('typeId', details['activityTypeDTO']) else None
    summary['activityType']['typeKey'] = details['activityTypeDTO']['typeKey'] if 'activityTypeDTO' in details and present('typeKey', details['activityTypeDTO']) else None
    summary['activityType']['parentTypeId'] = details['activityTypeDTO']['parentTypeId'] if 'activityTypeDTO' in details and present('parentTypeId', details['activityTypeDTO']) else None
    summary['eventType'] = {}
    summary['eventType']['typeKey'] = details['eventType']['typeKey'] if 'eventType' in details and present('typeKey', details['eventType']) else None
    summary['startTimeLocal'] = details['summaryDTO']['startTimeLocal'] if 'summaryDTO' in details and 'startTimeLocal' in details['summaryDTO'] else None
    summary['startTimeGMT'] = details['summaryDTO']['startTimeGMT'] if 'summaryDTO' in details and 'startTimeGMT' in details['summaryDTO'] else None
    summary['duration'] = details['summaryDTO']['duration'] if 'summaryDTO' in details and 'duration' in details['summaryDTO'] else None
    summary['distance'] = details['summaryDTO']['distance'] if 'summaryDTO' in details and 'distance' in details['summaryDTO'] else None
    summary['averageSpeed'] = details['summaryDTO']['averageSpeed'] if 'summaryDTO' in details and 'averageSpeed' in details['summaryDTO'] else None
    summary['maxHR'] = details['summaryDTO']['maxHR'] if 'summaryDTO' in details and 'maxHR' in details['summaryDTO'] else None
    summary['averageHR'] = details['summaryDTO']['averageHR'] if 'summaryDTO' in details and 'averageHR' in details['summaryDTO'] else None
    summary['elevationCorrected'] = details['metadataDTO']['elevationCorrected'] if 'metadataDTO' in details and 'elevationCorrected' in details['metadataDTO'] else None

def main(args):
    """
    Main entrypoint for script.
    """
    args = parse_arguments(args)
    setup_logging(args)
    logging.info("Starting %s version %s, usin Python version %s", args[0], SCRIPT_VERSION, python_version())
    logging_verbosity(args.verbosity)

    print('Welcome to Garmin Connect Exporter')

    if sys.version_info.major < 3:
        print('Please upgrade to Python 3.x version', python_version(), "isn't supported anymore.")
        sys.exit(1)

    # Get filter list with IDs to exclude
    if args.exclude is not None:
        exclude_list = read_exclude(args.exclude)
        if exclude_list is None:
            sys.exit(1)
    else:
        exclude_list = []

    if os.path.isdir(args.directory):
        logging.warning('Output directory %s already exists. Skipping already-downloaded files and appending them to the CSV file.', args.directory)
    else:
        os.mkdir(args.directory)

    login_to_garmin_connect(args)

    csv_filename = args.directory + '/activities.csv'
    csv_existed = os.path.isfile(csv_filename)

    csv_file = open(csv_filename, mode='a', encoding='utf-8')
    csv_filter = CsvFilter(csv_file, args.template)

    # write header to CSV file
    if not csv_existed:
        csv_filter.write_header()

    # Query the userstats (activities totals on the profile page) that are needed for filtering and for downloading 'all'
    userstats_json = fetch_userstats(args)

    if args.count == 'all':
        total_to_download = int(userstats_json['userMetrics'][0]['totalActivities'])
    else:
        total_to_download = int(args.count)

    device_dict = dict()

    activity_type_properties = http_req_as_string(URL_GC_ACT_PROPS)
    if args.verbosity > 0:
        write_to_file(os.path.join(args.directory, 'activity_types.properties'), activity_type_properties, 'w')
    activity_type_name = load_properties(activity_type_properties)
    event_type_properties = http_req_as_string(URL_GC_EVT_PROPS)
    if args.verbosity > 0:
        write_to_file(os.path.join(args.directory, 'event_types.properties'), activity_type_properties, 'w')
    event_type_name = load_properties(event_type_properties)

    activities = fetch_activity_list(args, total_to_download)
    action_list = annotate_activity_list(activities, args.start_activity_no, exclude_list)

    for item in action_list:
        current_index = item['index'] + 1
        activity = item['activity']
        action = item['action']

        # Action: skipping
        if action == 's':
            print('Skipping     : Garmin Connect activity ', end='')
            print(f"({current_index}/{len(action_list)}) [{activity['activityId']}]")
            continue

        # Action: excluding
        if action == 'e':
            print('Excluding    : Garmin Connect activity ', end='')
            print(f"({current_index}/{len(action_list)}) [{activity['activityId']}]")
            continue

        # Action: download
        print('Downloading: Garmin Connect activity ', end='')
        print(f"({current_index}/{len(action_list)}) [{activity['activityId']}] {activity['activityName']}")

        # Retrieve also the detail data from the activity
        activity_details, details = fetch_details(activity['activityId'], http_req_as_string)

        extract = {}
        extract['start_time_with_offset'] = offset_date_time(activity['startTimeLocal'], activity['startTimeGMT'])
        elapsed_duration = details['summaryDTO']['elapsedDuration'] if 'summaryDTO' in details and 'elapsedDuration' in details ['summaryDTO'] else None
        extract['elapsed_duration'] = elapsed_duration if elapsed_duration else activity['duration']
        extract['elapsed_seconds'] = int(round(extract['elapsed_duration']))
        extract['end_time_with_offset'] = extract['start_time_with_offset'] + timedelta(seconds=extract['elapsed_seconds'])

        print('\t', extract['start_time_with_offset'].isoformat(), ', ', sep='', end='')
        print(hhmmss_from_seconds(extract['elapsed_seconds']), ', ', sep='', end='')
        if 'distance' in activity and isinstance(activity['distance'], (float)):
            print("{0:.3f}".format(activity['distance']/1000), 'km', sep='')
        else:
            print('0.000 km')

        if args.desc is not None:
            append_desc = '_' + sanitize_filename(activity['activityName'], args.desc)
        else:
            append_desc = ''

        if args.originaltime:
            start_time_seconds = epoch_seconds_from_summary(activity)
        else:
            start_time_seconds = None

        extract['device'] = extract_device(device_dict, details, start_time_seconds, args, http_req_as_string, write_to_file)

        # try to get the JSON with all the samples
        extract['samples'] = None
        if csv_filter.is_column_active('sampleCount'):
            try:
                activity_measurements = http_req_as_string(f"{URL_GC_ACTIVITY}{activity['activityId']}/details")
                write_to_file(os.path.join(args.directory, f"activity {activity['activityId']}_samples.json"), activity_measurements, 'w', start_time_seconds)
                samples = json.loads(activity_measurements)
                extract['samples'] = samples
            except HTTPError:
                pass

        extract['gear'] = None
        if csv_filter.is_column_active('gear'):
            extract['gear'] = load_gear(str(activity['activityId']), args)

        extract['hrZones'] = HR_ZONES_EMPTY
        if csv_filter.is_column_active('hrZone1Low') or csv_filter.is_column_active('hrZone1Seconds'):
            extract['hrZones'] = load_zones(str(activity['activityId']), start_time_seconds, args, http_req_as_string, write_to_file)

        # Save the file and log if it already existed. If yes, do not append the record to the CSV
        if export_data_file(str(activity['activityId']), activity_details, args, start_time_seconds, append_desc, activity['startTimeLocal']):
            csv_write_record(csv_filter, extract, activity, details, activity_type_name, event_type_name)

    csv_file.close()

    if args.external:
        print('Open CSV output')
        print(csv_filename)
        call([args.external, "--" + args.args, csv_filename])

    print('Done!')

if __name__ == "__main__":
    try:
        main(sys.argv)
    except KeyboardInterrupt:
        print('Interrupted')
        sys.exit(0)
