#!/bin/bash

# Usage: just enter the new hash bellow, and run the script from the root of
# the repository. Note that the script is self-modifying: it will change the
# old hash into the new one, and erase the new hash again.

OLD_HASH=8ef169cd84584f3b3e234333d7dd8cfc65c5b78d
NEW_HASH=

sed -i "s/${OLD_HASH}/${NEW_HASH}/g" README.md DEVELOPERS.md .gitlab-ci.yml update_cerberus.sh
sed -i "s/^NEW_HASH=.*/NEW_HASH=/g" update_cerberus.sh

opam pin remove -y cerberus
opam pin add -n -y cerberus "git+https://github.com/rems-project/cerberus.git#${NEW_HASH}"
