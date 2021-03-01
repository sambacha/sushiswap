#!/usr/bin/env bash

targets="
contracts/MasterChefV2.sol
contracts/SushiBar.sol
contracts/SushiMaker.sol
contracts/SushiRoll.sol
contracts/SushiToken.sol
"

for target in ${targets}; do

  solc --overwrite --bin --abi \
        -o build  \
        "${target}".sol

done

for target in ${targets}; do

    web3j solidity generate \
        -b build/"${target}".bin \
        -a build/"${target}".abi \
        -o ../java \
        -p namespace.contracts.generated

    solc --bin-runtime --overwrite -o . ./"${target}".sol
done
