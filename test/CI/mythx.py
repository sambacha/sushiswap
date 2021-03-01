"""
@file: Solidity Mythril CI/CD Processor
@summary: Checks the Solidity files in repo using
Mythril and fails the build if there are errors in solidity files
@version 1.0.0
@SPDX-License-Identifier: MIT
"""

from glob import glob
from json import load
from os import getcwd
from os.path import exists
from subprocess import check_output

import re

# Check if configuration file exists and fetch values from it
if exists("sharkci.json"):
    data = load(open("sharkci.json"))
    if "FAIL_ON_WARNING" in data and isinstance(data["FAIL_ON_WARNING"], bool):
        FAIL_ON_WARNING = data["FAIL_ON_WARNING"]
    else:
        FAIL_ON_WARNING = False
    if "FAIL_ON_FIRST_ERROR" in data and isinstance(data["FAIL_ON_FIRST_ERROR"], bool):
        FAIL_ON_FIRST_ERROR = data["FAIL_ON_FIRST_ERROR"]
    else:
        FAIL_ON_FIRST_ERROR = False
    # TODO NOT YET IMPLEMENTED - WIP 
    if "IS_HARDHAT_PROJECT" in data and isinstance(data["IS_HARDHAT_PROJECT"], bool):
        IS_HARDHAT_PROJECT = data["IS_HARDHAT_PROJECT"]
    else:
        IS_HARDHAT_PROJECT = False
else:
    FAIL_ON_WARNING = False
    FAIL_ON_FIRST_ERROR = False
    IS_HARDHAT_PROJECT = False

log = open("test-results.log", "w")
FAIL_BUILD = False  # Specifies if the build has to be failed

# Handling truffle projects

if IS_HARDHAT_PROJECT:
    log.write("Processing Truffle Project\n")
    RESULT = check_output(["myth", "--truffle"]).decode("utf-8")
    log.write(RESULT)
    log.write("\nProcessing of Truffle Project Completed")
    if re.search("Error", RESULT, re.IGNORECASE):
        log.write("\nFound Error in Solidity Code. Failing Build")
        exit(1)

# Get all Solidity files in the repository
files = glob(getcwd() + "/**/*.sol", recursive=True)

# Process each file individually and check for errors / warnings as set
for file in files:
    log.write("Processing file " + file + "\n")
    #  myth analyze contracts/MasterChefV2.sol -o jsonv2 --enable-coverage-strategy
    # add your commands here for `check_output`
    RESULT = check_output(
        ["myth", "analyze", file], "--enable-coverage-strategy"
    ).decode("utf-8")
    log.write(RESULT)
    log.write("\nProcessing of file " + file + " Completed\n\n")
    if re.search("Error", RESULT, re.IGNORECASE) or (
            FAIL_ON_WARNING and re.search("Warning", RESULT, re.IGNORECASE)
    ):
        if FAIL_ON_FIRST_ERROR:
            log.write("\n-----Failing Build Since Fail on first error is enabled----\n")
            log.close()
            exit(1)
        else:
            FAIL_BUILD = True

# If there are errors or warnings (as per the config), Fail the build
if FAIL_BUILD:
    log.write(" 🆘 Failing build since Errors / Warnings (if set) are found in the Code")
    log.close()
    exit(1)

log.write(" ✅ Build passed since no issues were found")
log.write(" ✅ Build passed since no issues were found")
log.close()
