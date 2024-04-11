//SPDX-License-Identifier: MIT Licensed
// File: @openzeppelin/contracts/utils/Context.sol


// OpenZeppelin Contracts (last updated v5.0.1) (utils/Context.sol)

pragma solidity 0.8.20;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}

// File: @openzeppelin/contracts/access/Ownable.sol


// OpenZeppelin Contracts (last updated v5.0.0) (access/Ownable.sol)



/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * The initial owner is set to the address provided by the deployer. This can
 * later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    /**
     * @dev The caller account is not authorized to perform an operation.
     */
    error OwnableUnauthorizedAccount(address account);

    /**
     * @dev The owner is not a valid owner account. (eg. `address(0)`)
     */
    error OwnableInvalidOwner(address owner);

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the address provided by the deployer as the initial owner.
     */
    constructor(address initialOwner) {
        if (initialOwner == address(0)) {
            revert OwnableInvalidOwner(address(0));
        }
        _transferOwnership(initialOwner);
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        if (owner() != _msgSender()) {
            revert OwnableUnauthorizedAccount(_msgSender());
        }
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby disabling any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        if (newOwner == address(0)) {
            revert OwnableInvalidOwner(address(0));
        }
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

// File: @openzeppelin/contracts/access/Ownable2Step.sol


// OpenZeppelin Contracts (last updated v5.0.0) (access/Ownable2Step.sol)

/**
 * @dev Contract module which provides access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * The initial owner is specified at deployment time in the constructor for `Ownable`. This
 * can later be changed with {transferOwnership} and {acceptOwnership}.
 *
 * This module is used through inheritance. It will make available all functions
 * from parent (Ownable).
 */
abstract contract Ownable2Step is Ownable {
    address private _pendingOwner;

    event OwnershipTransferStarted(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Returns the address of the pending owner.
     */
    function pendingOwner() public view virtual returns (address) {
        return _pendingOwner;
    }

    /**
     * @dev Starts the ownership transfer of the contract to a new account. Replaces the pending transfer if there is one.
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual override onlyOwner {
        _pendingOwner = newOwner;
        emit OwnershipTransferStarted(owner(), newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`) and deletes any pending owner.
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual override {
        delete _pendingOwner;
        super._transferOwnership(newOwner);
    }

    /**
     * @dev The new owner accepts the ownership transfer.
     */
    function acceptOwnership() public virtual {
        address sender = _msgSender();
        if (pendingOwner() != sender) {
            revert OwnableUnauthorizedAccount(sender);
        }
        _transferOwnership(sender);
    }
}


// File: mainnet/0xe0233670f696795067d40fd2d9dd99c3f3b88ef1/openzeppelin-contracts/contracts/token/ERC20/extensions/draft-IERC20Permit.sol


// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/draft-IERC20Permit.sol)


/**
 * @dev Interface of the ERC20 Permit extension allowing approvals to be made via signatures, as defined in
 * https://eips.ethereum.org/EIPS/eip-2612[EIP-2612].
 *
 * Adds the {permit} method, which can be used to change an account's ERC20 allowance (see {IERC20-allowance}) by
 * presenting a message signed by the account. By not relying on {IERC20-approve}, the token holder account doesn't
 * need to send a transaction, and thus is not required to hold Ether at all.
 */
interface IERC20Permit {
    /**
     * @dev Sets `value` as the allowance of `spender` over ``owner``'s tokens,
     * given ``owner``'s signed approval.
     *
     * IMPORTANT: The same issues {IERC20-approve} has related to transaction
     * ordering also apply here.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `deadline` must be a timestamp in the future.
     * - `v`, `r` and `s` must be a valid `secp256k1` signature from `owner`
     * over the EIP712-formatted function arguments.
     * - the signature must use ``owner``'s current nonce (see {nonces}).
     *
     * For more information on the signature format, see the
     * https://eips.ethereum.org/EIPS/eip-2612#specification[relevant EIP
     * section].
     */
    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;

    /**
     * @dev Returns the current nonce for `owner`. This value must be
     * included whenever a signature is generated for {permit}.
     *
     * Every successful call to {permit} increases ``owner``'s nonce by one. This
     * prevents a signature from being used multiple times.
     */
    function nonces(address owner) external view returns (uint256);

    /**
     * @dev Returns the domain separator used in the encoding of the signature for {permit}, as defined by {EIP712}.
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}

// File: mainnet/0xe0233670f696795067d40fd2d9dd99c3f3b88ef1/openzeppelin-contracts/contracts/token/ERC20/IERC20.sol


// OpenZeppelin Contracts (last updated v4.6.0) (token/ERC20/IERC20.sol)

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);
}

// File: mainnet/0xe0233670f696795067d40fd2d9dd99c3f3b88ef1/openzeppelin-contracts/contracts/token/ERC20/utils/SafeERC20.sol


// OpenZeppelin Contracts (last updated v4.8.0) (token/ERC20/utils/SafeERC20.sol)





abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        _nonReentrantBefore();
        _;
        _nonReentrantAfter();
    }

    function _nonReentrantBefore() private {
        // On the first call to nonReentrant, _status will be _NOT_ENTERED
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;
    }

    function _nonReentrantAfter() private {
        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Returns true if the reentrancy guard is currently set to "entered", which indicates there is a
     * `nonReentrant` function in the call stack.
     */
    function _reentrancyGuardEntered() internal view returns (bool) {
        return _status == _ENTERED;
    }
}

interface AggregatorV3Interface {
    function decimals() external view returns (uint8);

    function description() external view returns (string memory);

    function version() external view returns (uint256);

    function getRoundData(uint80 _roundId)
        external
        view
        returns (
            uint80 roundId,
            int256 answer,
            uint256 startedAt,
            uint256 updatedAt,
            uint80 answeredInRound
        );

    function latestRoundData()
        external
        view
        returns (
            uint80 roundId,
            int256 answer,
            uint256 startedAt,
            uint256 updatedAt,
            uint80 answeredInRound
        );
}

contract HELLDIVER_Presale is ReentrancyGuard, Ownable2Step {

    IERC20 public mainToken;
    IERC20 public USDT;
    IERC20 public USDC;

    AggregatorV3Interface public priceFeed;

    // Stats
    uint256 public soldToken;
    uint256 public amountRaised;
    uint256 public amountRaisedUSDT;
    uint256 public amountRaisedUSDC;
    uint256 public amountRaisedOverall;
    uint256 public uniqueBuyers;

    address payable public fundReceiver;

    bool public presaleStatus;
    bool public isPresaleEnded;
    uint256 public claimStartTime;
    uint256 public launchTime;

    struct Phase {
        uint256 totalSoldTokens;
        uint256 amountRaised;
    }
    uint256[] public prices = [
        77579519006982,
        52328623757195,
        39463299131807,
        31685678073510,
        26469031233456,
        22727272727272,
        19912385503783,
        17717930545712,
        15956598053295,
        14515894904920,
        13313806417254,
        12295585884667,
        11420740063956,
        10663254425250,
        10000000000000
    ];
    uint256 public totalStages = 15;
    uint256 public APY = 500_00;
    uint256 public percentDivider = 100_00;
    uint256 public timeStep = 365 days;
    uint256 public tokensToSell = 3_625_000_000e9;

    address[] public UsersAddresses;

    struct User {
        uint256 native_balance;
        uint256 usdt_balance;
        uint256 usdc_balance;
        uint256 token_balance;
        uint256 stakeCount;
    }

    struct StakeData {
        uint256 stakedTokens;
        uint256 claimedTokens;
        uint256 stakeTime;
        uint256 userApy;
        uint256 claimedReward;
        bool isUnstake;
        uint256 unstakeTime;
    }

    mapping(address => User) public users;
    mapping(address => mapping(uint256 => StakeData)) public userStakes;
    mapping(address => bool) public isExist;
    mapping(uint256 => Phase) public phases;

    event BuyToken(address indexed _user, uint256 indexed _amount);
    event ClaimToken(address indexed _user, uint256 indexed _amount);
    event ChnageStableToken(IERC20 indexed  _usdt, IERC20 indexed  _usdc);
    event Stake(address indexed user, uint256 indexed amount);

    constructor(IERC20 _token, address _fundReceiver, address _USDC, address _USDT, address _priceFeedAggregator )Ownable(msg.sender) {
        mainToken = _token;
        USDT = IERC20(_USDT);
        USDC = IERC20(_USDC);
        fundReceiver = payable(_fundReceiver);
        priceFeed = AggregatorV3Interface(_priceFeedAggregator);
    }

    // to get real time price of Eth
    function getLatestPrice() public view returns (uint256) {
        (, int256 price, , , ) = priceFeed.latestRoundData();
        return uint256(price);
    }

    // to buy token during preSale time with Eth => for web3 use
    function buyToken() public payable nonReentrant {
        require(!isPresaleEnded, "Presale ended!");
        require(presaleStatus, " Presale is Paused!");
        if (!isExist[msg.sender]) {
            isExist[msg.sender] = true;
            uniqueBuyers++;
            UsersAddresses.push(msg.sender);
        }

        bool sent = fundReceiver.send(msg.value);
        require(sent, "Failed to send Ether");

        uint256 numberOfTokens;
        (uint256 price, ) = getpriceAndStage();
        (, uint256 phase) = getpriceAndStage();
        numberOfTokens = nativeToToken(msg.value, price);
        require(soldToken + numberOfTokens <= tokensToSell, "Limit Reached");

        soldToken = soldToken + (numberOfTokens);
        amountRaised = amountRaised + (msg.value);
        amountRaisedOverall = amountRaisedOverall + BnbToUsdt(msg.value);

        users[msg.sender].native_balance =
            users[msg.sender].native_balance +
            (msg.value);
        users[msg.sender].token_balance =
            users[msg.sender].token_balance +
            (numberOfTokens);
        phases[phase].totalSoldTokens += numberOfTokens;
        phases[phase].amountRaised += BnbToUsdt(msg.value);
        stake(numberOfTokens);
        users[msg.sender].stakeCount++;
        emit BuyToken(msg.sender, msg.value);
    }

    // to buy token during preSale time with USDT => for web3 use
    function buyTokenUSDT(uint256 amount) public nonReentrant {
        require(!isPresaleEnded, "Presale ended!");
        require(presaleStatus, " Presale is Paused!");
        if (!isExist[msg.sender]) {
            isExist[msg.sender] = true;
            uniqueBuyers++;
            UsersAddresses.push(msg.sender);
        }
        bool success = USDT.transferFrom(msg.sender, fundReceiver, amount);
        if(!success){
            revert("Transfer failed");
        }

        uint256 numberOfTokens;
        (uint256 price, ) = getpriceAndStage();
        (, uint256 phase) = getpriceAndStage();
        numberOfTokens = usdtToToken(amount, price);
        require(soldToken + numberOfTokens <= tokensToSell, "Limit Reached");
        soldToken = soldToken + numberOfTokens;
        amountRaisedUSDT = amountRaisedUSDT + amount;
        amountRaisedOverall = amountRaisedOverall + amount;

        users[msg.sender].usdt_balance += amount;

        users[msg.sender].token_balance =
            users[msg.sender].token_balance +
            numberOfTokens;
        phases[phase].totalSoldTokens += numberOfTokens;
        phases[phase].amountRaised += amount;
        stake(numberOfTokens);
        users[msg.sender].stakeCount++;
        emit BuyToken(msg.sender, amount);
    }

    // to buy token during preSale time with USDT => for web3 use
    function buyTokenUSDC(uint256 amount) public nonReentrant{
        require(!isPresaleEnded, "Presale ended!");
        require(presaleStatus, " Presale is Paused!");
        if (!isExist[msg.sender]) {
            isExist[msg.sender] = true;
            uniqueBuyers++;
            UsersAddresses.push(msg.sender);
        }
        bool success = USDC.transferFrom(msg.sender, fundReceiver, amount);
        if(!success){
            revert("Transfer failed");
        }

        uint256 numberOfTokens;
        (uint256 price, ) = getpriceAndStage();
        (, uint256 phase) = getpriceAndStage();
        numberOfTokens = usdtToToken(amount, price);
        require(soldToken + numberOfTokens <= tokensToSell, "Limit Reached");
        soldToken = soldToken + numberOfTokens;
        amountRaisedUSDC = amountRaisedUSDC + amount;
        amountRaisedOverall = amountRaisedOverall + amount;

        users[msg.sender].usdc_balance += amount;

        users[msg.sender].token_balance =
            users[msg.sender].token_balance +
            numberOfTokens;
        phases[phase].totalSoldTokens += numberOfTokens;
        phases[phase].amountRaised += amount;
        stake(numberOfTokens);
        users[msg.sender].stakeCount++;
        emit BuyToken(msg.sender, amount);
    }

    function getpriceAndStage()
        public
        view
        returns (uint256 _price, uint256 phase)
    {
        uint256 duration = block.timestamp - launchTime;
        phase = duration / 10 days;
        if (phase > totalStages - 1) {
            phase = totalStages - 1;
        }
        _price = prices[phase];
    }

    function stake(uint256 _amount) internal {
        User storage user = users[msg.sender];
        StakeData storage userStake = userStakes[msg.sender][user.stakeCount];
        userStake.stakedTokens = _amount;
        userStake.stakeTime = block.timestamp;
        userStake.userApy = APY;

        emit Stake(msg.sender, _amount);
    }

    function calculateReward(address _user, uint256 _index)
        public
        view
        returns (uint256 _reward)
    {
        StakeData memory userStake = userStakes[_user][_index];
        uint256 rewardDuration = block.timestamp - (userStake.stakeTime);
        _reward =
            (userStake.stakedTokens * (rewardDuration) * (userStake.userApy)) /
            (percentDivider * (timeStep));
    }

    function Unstake(uint256 _index) public nonReentrant{
        require(isPresaleEnded, "Presale not ended!");
        StakeData storage userStake = userStakes[msg.sender][_index];
        require(!userStake.isUnstake, "Already withdrawn");
        uint256 _reward = calculateReward(msg.sender, _index);
        if (_reward > 0) {
            (bool success) = mainToken.transfer(msg.sender, _reward);
            require(success, "token transfer failed");
            userStake.claimedReward += _reward;
        }
        (bool status) = mainToken.transfer(msg.sender, userStake.stakedTokens);
        require(status, "token transfer failed");
        userStake.claimedTokens = userStake.stakedTokens;
        userStake.unstakeTime = block.timestamp;
        emit ClaimToken(msg.sender,userStake.stakedTokens);
    }

    function getPhaseDetail(uint256 phaseInd)
        external
        view
        returns (uint256 _tokenToSell, uint256 _amountRaised)
    {
        Phase memory phase = phases[phaseInd];
        return (phase.totalSoldTokens, phase.amountRaised);
    }

    function startPresale() external onlyOwner payable {
        presaleStatus = true;
        launchTime = block.timestamp;
    }

    function endPresale() external onlyOwner payable {
        isPresaleEnded = true;
        claimStartTime = block.timestamp;
    }

    // to check number of token for given BNB
    function nativeToToken(uint256 _amount, uint256 price)
        public
        view
        returns (uint256)
    {
        uint256 bnbToUsdt = (_amount * (getLatestPrice())) / (1 ether);
        uint256 numberOfTokens = (bnbToUsdt * price) / (1e8);
        return numberOfTokens;
    }

    // BNB to USD
    function BnbToUsdt(uint256 _amount) public view returns (uint256) {
        uint256 bnbToUsdt = (_amount * (getLatestPrice())) / (1e8);
        return bnbToUsdt;
    }

    // to check number of token for given usdt
    function usdtToToken(uint256 _amount, uint256 price)
        public
        pure
        returns (uint256)
    {
        uint256 numberOfTokens = (_amount * price) / (1e18);
        return numberOfTokens;
    }

    function updateInfos(
        uint256 _sold,
        uint256 _raised,
        uint256 _raisedInUsdt,
        uint256 _raisedInUsdc,
        uint256 _amountRaisedOverall
    ) external onlyOwner {
        soldToken = _sold;
        amountRaised = _raised;
        amountRaisedUSDT = _raisedInUsdt;
        amountRaisedUSDC = _raisedInUsdc;
        amountRaisedOverall = _amountRaisedOverall;
    }

    // change tokens
    function updateToken(address _token) external onlyOwner payable{
        mainToken = IERC20(_token);
    }

    //change tokens for buy
    function updateStableTokens(IERC20 _USDT, IERC20 _USDC) external onlyOwner payable {
        USDT = IERC20(_USDT);
        USDC = IERC20(_USDC);
        emit ChnageStableToken(_USDT, _USDC);
    }

    //for changing APY => add two exrra zero
    function changeAPY(uint256 _APY) public onlyOwner payable {
        APY = _APY;
    }

    // to withdraw funds for liquidity
    function initiateTransfer(uint256 _value) external onlyOwner payable {
        bool sent = fundReceiver.send(_value);
        require(sent, "Failed to send Ether");
    }

    // to withdraw funds for liquidity
    function changeFundReceiver(address _addr) external onlyOwner payable {
        fundReceiver = payable(_addr);
    }

    // to withdraw funds for liquidity
    function updatePriceFeed(AggregatorV3Interface _priceFeed)
        external
        onlyOwner
        payable
    {
        priceFeed = _priceFeed;
    }

    // to withdraw out tokens
    function transferTokens(IERC20 token, uint256 _value) external onlyOwner payable {
        (bool success) = token.transfer(msg.sender, _value);
        require(success, "token transfer failed");
    }

    function totalUsersCount() external view returns (uint256) {
        return UsersAddresses.length;
    }
}
