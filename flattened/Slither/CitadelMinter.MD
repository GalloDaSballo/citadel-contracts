entreprenerd@MacBook-Pro citadel-contracts % slither flattened/CitadelMinter.sol 



Acknowledged, really not worried about the event
Reentrancy in CitadelMinter._transferToFundingPools(uint256) (flattened/CitadelMinter.sol#2016-2037):
	External calls:
	- IERC20Upgradeable(address(citadelToken)).safeTransfer(pool,amount) (flattened/CitadelMinter.sol#2028)
	Event emitted after the call(s):
	- CitadelDistributionToFundingPool(lastMintTimestamp,block.timestamp,pool,amount) (flattened/CitadelMinter.sol#2030-2035)


Reentrancy in CitadelMinter.mintAndDistribute() (flattened/CitadelMinter.sol#1842-1915)
-> We have nonReentrant



CitadelMinter.initializeLastMintTimestamp() (flattened/CitadelMinter.sol#1992-2009) uses timestamp for comparisons
	Dangerous comparisons:
	- require(bool,string)(lastMintTimestamp == 0,CitadelMinter: last mint timestamp already initialized) (flattened/CitadelMinter.sol#1997-2000)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#block-timestamp



GlobalAccessControlManaged.gacPausable() (flattened/CitadelMinter.sol#1533-1537) compares to a boolean constant:
	-require(bool,string)(gac.paused() == false,global-paused) (flattened/CitadelMinter.sol#1534)
GlobalAccessControlManaged.gacPausable() (flattened/CitadelMinter.sol#1533-1537) compares to a boolean constant:
	-require(bool,string)(paused() == false,local-paused) (flattened/CitadelMinter.sol#1535)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#boolean-equality
