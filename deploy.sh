#! /bin/bash
#
# deploy.sh
# Copyright (C) 2016 Subho Halder <subho.halder@gmail.com>
#
# Distributed under terms of the MIT license.
#


rm -rf dist/
bumpversion patch
python setup.py sdist
twine upload dist/*
