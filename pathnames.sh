#!/bin/sh
git grep -l '@boringcrypto' ':!*.json' | xargs gsed -i 's/@boringcrypto/node_modules\/@boringcrypto/g'
