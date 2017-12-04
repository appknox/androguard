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
python setup.py bdist_wheel
twine upload dist/*
git push origin deploy
git push origin deploy --tags
