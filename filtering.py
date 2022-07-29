"""
doc
"""

import logging

from os import path

import json

from requests import JSONDecodeError

DOWNLOADED_IDS_FILE_NAME = "downloaded_ids.json"
KEY_IDS = "ids"


def read_exclude(file):
    """
    # to do
    """

    if not path.exists(file):
        print(f'File not found: {file}')
        return

    if not path.isfile(file):
        print(f'Not a file: {file}')
        return

    with open(file, 'r') as f:
        try:
            obj = json.load(f)
            return obj['ids']
        except (JSONDecodeError, ValueError):
            print(f"There is no valid JSON in {file}")
            return


def update_download_stats(activity_id, dir):
    """
    Function for adding item to download_stats file, only if not already there. This function should be called for each successfully downloaded activity.
    The statistic is independent of the downloaded file type.

    :param activity_id: string with activity ID
    :param dir: download root directory
    """
    file = path.join(dir, DOWNLOADED_IDS_FILE_NAME)

    # first time handling
    if not path.exists(file):
        with open(file, 'w') as read_obj:
            read_obj.write(json.dumps(""))

    # read file
    with open(file, 'r') as read_obj:
        data = read_obj.read()

        try:
            obj = json.loads(data)

        except (JSONDecodeError, ValueError):
            obj = ""

    # sainitize wrong formats
    if not type(obj) is dict:
        obj = {}

    if KEY_IDS not in obj:
        obj[KEY_IDS] = []

    if activity_id in obj[KEY_IDS]:
        logging.info("%s already in %s", activity_id, file)
        return

    obj[KEY_IDS].append(activity_id)
    obj[KEY_IDS].sort()

    with open(file, 'w') as write_obj:
        write_obj.write(json.dumps(obj))
