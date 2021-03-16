# SafeTransfer simplification
sed -i 's/safeT/t/g' contracts/MasterChefV2.sol

# Virtualize functions
#perl -0777 -i -pe 's/public payable \{/public virtual payable \{/g' node_modules/@sushiswap/bentobox-sdk/contracts/BentoBoxV1.sol

# private constant
#perl -0777 -i -pe 's/private constant / public constant /g' contracts/flat/KashiPairFlat.sol 

# Virtualize modifier
#perl -0777 -i -pe 's/modifier solvent\(\) \{/ modifier solvent\(\) virtual \{ /g' contracts/flat/KashiPairFlat.sol 

# Add transfer function declaration 
perl -0777 -i -pe 's/\}/function transfer\(address to, uint256 amount\) external;\n function transferFrom\(address from, address to, uint256 amount\) external;\n\}/g' node_modules/@boringcrypto/boring-solidity/contracts/interfaces/IERC20.sol
