# For windows replace certoraRun -> certoraRun.py and you might want to add --solc
certoraRun  spec/harnesses/MasterChefV2Harness.sol spec/harnesses/DummyERC20A.sol spec/harnesses/DummyERC20B.sol \
			--verify MasterChefV2Harness:spec/MasterChefV2.spec \
			--staging 
