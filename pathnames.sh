#!/bin/sh
git grep -l '@boringcrypto' | xargs gsed -i 's/@boringcrypto/node_modules\/@boringcrypto/g'
