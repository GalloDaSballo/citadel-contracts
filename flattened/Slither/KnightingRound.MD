
Acknowledged, who cares about event
Reentrancy in KnightingRound.buy(uint256,uint8,bytes32[]) (flattened/KnightingRound.sol#1507-1549):
	External calls:
	- tokenIn.safeTransferFrom(msg.sender,saleRecipient,_tokenInAmount) (flattened/KnightingRound.sol#1546)
	Event emitted after the call(s):
	- Sale(msg.sender,_daoId,_tokenInAmount,tokenOutAmount_) (flattened/KnightingRound.sol#1548)

Acknowledged, who cares about event
Reentrancy in KnightingRound.claim() (flattened/KnightingRound.sol#1554-1568):
	External calls:
	- tokenOut.safeTransfer(msg.sender,tokenOutAmount_) (flattened/KnightingRound.sol#1565)
	Event emitted after the call(s):
	- Claim(msg.sender,tokenOutAmount_) (flattened/KnightingRound.sol#1567)

Acknowledged, who cares about event
Reentrancy in KnightingRound.sweep(address) (flattened/KnightingRound.sol#1747-1762):
	External calls:
	- ERC20Upgradeable(_token).safeTransfer(saleRecipient,amount) (flattened/KnightingRound.sol#1759)
	Event emitted after the call(s):
	- Sweep(_token,amount) (flattened/KnightingRound.sol#1761)



KnightingRound.initialize(address,address,address,uint256,uint256,uint256,address,address,uint256) (flattened/KnightingRound.sol#1454-1494) uses timestamp for comparisons
	Dangerous comparisons:
	- require(bool,string)(_saleStart >= block.timestamp,KnightingRound: start date may not be in the past) (flattened/KnightingRound.sol#1465-1468)


99% sure it's fluke but will investigate
Manipulation of timestamp is up to [Prev_Block_Time, Block_After_time] which is about 13 seconds

KnightingRound.buy(uint256,uint8,bytes32[]) (flattened/KnightingRound.sol#1507-1549) uses timestamp for comparisons
	Dangerous comparisons:
	- require(bool,string)(saleStart <= block.timestamp,KnightingRound: not started) (flattened/KnightingRound.sol#1512)
	- require(bool,string)(block.timestamp < saleStart + saleDuration,KnightingRound: already ended) (flattened/KnightingRound.sol#1513-1516)
KnightingRound.saleEnded() (flattened/KnightingRound.sol#1603-1607) uses timestamp for comparisons
	Dangerous comparisons:
	- hasEnded_ = (block.timestamp >= saleStart + saleDuration) || (totalTokenIn >= tokenInLimit) (flattened/KnightingRound.sol#1604-1606)
KnightingRound.setSaleStart(uint256) (flattened/KnightingRound.sol#1634-1647) uses timestamp for comparisons
	Dangerous comparisons:
	- require(bool,string)(_saleStart >= block.timestamp,KnightingRound: start date may not be in the past) (flattened/KnightingRound.sol#1638-1641)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#block-timestamp