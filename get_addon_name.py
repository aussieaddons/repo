#!/usr/bin/env python
# prints the name of a Kodi add-on to stdout. Specify the path as an argument.
import xml.etree.ElementTree as ET
import sys
import os


def main():
    if len(sys.argv) > 1:
        if 'addon.xml' in sys.argv[1]:
            path = sys.argv[1]
        else:
            path = os.path.join(sys.argv[1], 'addon.xml')
    else:
        path = 'addon.xml'
    with open(path, 'r') as f:
        root = ET.fromstring(f.read())
        print root.attrib['name']


if __name__ == '__main__':
    main()
