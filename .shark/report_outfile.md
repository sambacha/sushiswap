## Sūrya's Description Report

### Files Description Table


|  File Name  |  SHA-1 Hash  |
|-------------|--------------|
| contracts/MasterChefV2.sol | 1dc498d101759f044f0c5fe5053cb8e719a8457b |


### Contracts Description Table


|  Contract  |         Type        |       Bases      |                  |                 |
|:----------:|:-------------------:|:----------------:|:----------------:|:---------------:|
|     └      |  **Function Name**  |  **Visibility**  |  **Mutability**  |  **Modifiers**  |
||||||
| **MasterChefV2** | Implementation | BoringOwnable, BoringBatchable |||
| └ | <Constructor> | Public ❗️ | 🛑  |NO❗️ |
| └ | init | External ❗️ | 🛑  |NO❗️ |
| └ | poolLength | Public ❗️ |   |NO❗️ |
| └ | add | Public ❗️ | 🛑  | onlyOwner |
| └ | set | Public ❗️ | 🛑  | onlyOwner |
| └ | pendingSushi | External ❗️ |   |NO❗️ |
| └ | massUpdatePools | External ❗️ | 🛑  |NO❗️ |
| └ | sushiPerBlock | Public ❗️ |   |NO❗️ |
| └ | updatePool | Public ❗️ | 🛑  |NO❗️ |
| └ | deposit | Public ❗️ | 🛑  |NO❗️ |
| └ | withdraw | Public ❗️ | 🛑  |NO❗️ |
| └ | harvest | Public ❗️ | 🛑  |NO❗️ |
| └ | harvestFromMasterChef | Public ❗️ | 🛑  |NO❗️ |
| └ | emergencyWithdraw | Public ❗️ | 🛑  |NO❗️ |


### Legend

|  Symbol  |  Meaning  |
|:--------:|-----------|
|    🛑    | Function can modify state |
|    💵    | Function is payable |
