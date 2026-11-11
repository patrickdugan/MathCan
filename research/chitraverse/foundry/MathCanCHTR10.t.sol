// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.24;

// Install under test/ of Uniswap/v4-core at the pinned commit in the CI workflow.
// This executes the real PoolManager + real tick crossing + permitted hook returns.
import {Deployers} from "./utils/Deployers.sol";
import {Vm} from "forge-std/Vm.sol";
import {MockERC20} from "solmate/src/test/utils/mocks/MockERC20.sol";
import {IERC20Minimal} from "../src/interfaces/external/IERC20Minimal.sol";
import {IPoolManager} from "../src/interfaces/IPoolManager.sol";
import {IHooks} from "../src/interfaces/IHooks.sol";
import {IUnlockCallback} from "../src/interfaces/callback/IUnlockCallback.sol";
import {Hooks} from "../src/libraries/Hooks.sol";
import {StateLibrary} from "../src/libraries/StateLibrary.sol";
import {TransientStateLibrary} from "../src/libraries/TransientStateLibrary.sol";
import {TickMath} from "../src/libraries/TickMath.sol";
import {Currency, CurrencyLibrary} from "../src/types/Currency.sol";
import {PoolKey} from "../src/types/PoolKey.sol";
import {PoolId, PoolIdLibrary} from "../src/types/PoolId.sol";
import {SwapParams, ModifyLiquidityParams} from "../src/types/PoolOperation.sol";
import {BalanceDelta, BalanceDeltaLibrary} from "../src/types/BalanceDelta.sol";
import {BeforeSwapDelta, toBeforeSwapDelta} from "../src/types/BeforeSwapDelta.sol";

contract MathCanReturnHook is IHooks {
    using BalanceDeltaLibrary for BalanceDelta;
    using TransientStateLibrary for IPoolManager;

    int128 public constant SPECIFIED_CUT = 1e15;
    int128 public constant BEFORE_UNSPECIFIED = 2e12;
    int128 public constant AFTER_UNSPECIFIED = 3e12;
    uint256 public beforeCalls;
    uint256 public afterCalls;
    int128 public lastPool0;
    int128 public lastPool1;

    function beforeSwap(address, PoolKey calldata, SwapParams calldata params, bytes calldata)
        external override returns (bytes4, BeforeSwapDelta, uint24)
    {
        require(params.zeroForOne && params.amountSpecified == -int256(5e16), "unexpected swap");
        ++beforeCalls;
        return (IHooks.beforeSwap.selector, toBeforeSwapDelta(SPECIFIED_CUT, BEFORE_UNSPECIFIED), 0);
    }

    function afterSwap(address, PoolKey calldata, SwapParams calldata, BalanceDelta delta, bytes calldata)
        external override returns (bytes4, int128)
    {
        ++afterCalls;
        lastPool0 = delta.amount0();
        lastPool1 = delta.amount1();
        return (IHooks.afterSwap.selector, AFTER_UNSPECIFIED);
    }

    // The hook's positive signed deltas are settled by actual PoolManager.take calls,
    // after PoolManager.swap has credited the hook and before unlock can relock.
    function collect(IPoolManager manager, Currency c0, Currency c1) external returns (int256 a0, int256 a1) {
        a0 = manager.currencyDelta(address(this), c0);
        a1 = manager.currencyDelta(address(this), c1);
        require(a0 >= 0 && a1 >= 0, "hook owes funds");
        if (a0 > 0) manager.take(c0, address(this), uint256(a0));
        if (a1 > 0) manager.take(c1, address(this), uint256(a1));
    }

    // Unused hook callbacks complete the IHooks interface. The deployed address
    // advertises only BEFORE_SWAP/AFTER_SWAP and their RETURNS_DELTA flags.
    function beforeInitialize(address, PoolKey calldata, uint160) external pure override returns (bytes4) {
        return IHooks.beforeInitialize.selector;
    }
    function afterInitialize(address, PoolKey calldata, uint160, int24) external pure override returns (bytes4) {
        return IHooks.afterInitialize.selector;
    }
    function beforeAddLiquidity(address, PoolKey calldata, ModifyLiquidityParams calldata, bytes calldata)
        external pure override returns (bytes4) { return IHooks.beforeAddLiquidity.selector; }
    function afterAddLiquidity(address, PoolKey calldata, ModifyLiquidityParams calldata, BalanceDelta, BalanceDelta, bytes calldata)
        external pure override returns (bytes4, BalanceDelta) {
        return (IHooks.afterAddLiquidity.selector, BalanceDelta.wrap(0));
    }
    function beforeRemoveLiquidity(address, PoolKey calldata, ModifyLiquidityParams calldata, bytes calldata)
        external pure override returns (bytes4) { return IHooks.beforeRemoveLiquidity.selector; }
    function afterRemoveLiquidity(address, PoolKey calldata, ModifyLiquidityParams calldata, BalanceDelta, BalanceDelta, bytes calldata)
        external pure override returns (bytes4, BalanceDelta) {
        return (IHooks.afterRemoveLiquidity.selector, BalanceDelta.wrap(0));
    }
    function beforeDonate(address, PoolKey calldata, uint256, uint256, bytes calldata)
        external pure override returns (bytes4) { return IHooks.beforeDonate.selector; }
    function afterDonate(address, PoolKey calldata, uint256, uint256, bytes calldata)
        external pure override returns (bytes4) { return IHooks.afterDonate.selector; }
}

contract MathCanHookRouter is IUnlockCallback {
    using StateLibrary for IPoolManager;
    using TransientStateLibrary for IPoolManager;
    using PoolIdLibrary for PoolKey;
    using CurrencyLibrary for Currency;

    IPoolManager public immutable manager;
    MathCanReturnHook public immutable hook;

    struct Observation {
        int256 poolDelta0;
        int256 poolDelta1;
        int256 callerDelta0;
        int256 callerDelta1;
        int256 hookDelta0;
        int256 hookDelta1;
        uint256 nonzeroAtSwap;
        uint256 nonzeroAfterSettlement;
        uint160 finalPrice;
        int24 finalTick;
        uint128 finalLiquidity;
    }

    constructor(IPoolManager _manager, MathCanReturnHook _hook) { manager = _manager; hook = _hook; }

    function execute(PoolKey calldata key, SwapParams calldata params) external returns (Observation memory) {
        return abi.decode(manager.unlock(abi.encode(msg.sender, key, params)), (Observation));
    }

    function unlockCallback(bytes calldata raw) external returns (bytes memory) {
        require(msg.sender == address(manager), "not PoolManager");
        (address payer, PoolKey memory key, SwapParams memory params) =
            abi.decode(raw, (address, PoolKey, SwapParams));
        Observation memory o;
        BalanceDelta delta = manager.swap(key, params, bytes("mathcan-chtr10"));
        o.callerDelta0 = delta.amount0();
        o.callerDelta1 = delta.amount1();
        o.poolDelta0 = hook.lastPool0();
        o.poolDelta1 = hook.lastPool1();
        o.hookDelta0 = o.poolDelta0 - o.callerDelta0;
        o.hookDelta1 = o.poolDelta1 - o.callerDelta1;
        o.nonzeroAtSwap = manager.getNonzeroDeltaCount();
        (o.hookDelta0, o.hookDelta1) = hook.collect(manager, key.currency0, key.currency1);
        int256 caller0 = manager.currencyDelta(address(this), key.currency0);
        int256 caller1 = manager.currencyDelta(address(this), key.currency1);
        require(caller0 == o.callerDelta0 && caller1 == o.callerDelta1, "caller delta changed");
        require(caller0 < 0 && caller1 > 0, "unexpected trade direction");
        manager.sync(key.currency0);
        require(IERC20Minimal(Currency.unwrap(key.currency0)).transferFrom(
            payer, address(manager), uint256(-caller0)), "ERC20 settle transfer failed");
        manager.settle();
        manager.take(key.currency1, payer, uint256(caller1));
        o.nonzeroAfterSettlement = manager.getNonzeroDeltaCount();
        PoolId id = key.toId();
        (o.finalPrice, o.finalTick,,) = manager.getSlot0(id);
        o.finalLiquidity = manager.getLiquidity(id);
        return abi.encode(o);
    }
}

contract MathCanCHTR10 is Deployers {
    using StateLibrary for IPoolManager;
    using TransientStateLibrary for IPoolManager;
    using PoolIdLibrary for PoolKey;
    using CurrencyLibrary for Currency;

    string internal constant CORE_COMMIT = "bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6";
    uint256 internal constant GROSS = 5e16;
    bytes32 internal constant NONZERO_SLOT =
        0x7d4b3164c6e45b97e7d87b7125a44c5828d005af88f9d751cfd78729c5d99a0b;
    MathCanHookRouter internal probe;
    MathCanReturnHook internal hook;

    function setUp() public {
        deployFreshManagerAndRouters();
        deployMintAndApprove2Currencies();
        address hookAddress = address(uint160(Hooks.BEFORE_SWAP_FLAG | Hooks.AFTER_SWAP_FLAG
            | Hooks.BEFORE_SWAP_RETURNS_DELTA_FLAG | Hooks.AFTER_SWAP_RETURNS_DELTA_FLAG));
        MathCanReturnHook implementation = new MathCanReturnHook();
        vm.etch(hookAddress, address(implementation).code); // permissioned deterministic test hook
        hook = MathCanReturnHook(hookAddress);
        (key,) = initPoolAndAddLiquidity(currency0, currency1, IHooks(hookAddress), 3000, SQRT_PRICE_1_1);
        // Four adjacent ranges. The swap crosses -120, -240, -360 before ending in [-480,-360).
        for (uint256 j = 1; j <= 3; ++j) {
            ModifyLiquidityParams memory range = ModifyLiquidityParams({
                tickLower: -int24(int256(120 * (j + 1))),
                tickUpper: -int24(int256(120 * j)),
                liquidityDelta: int256((j + 1) * 1e18), salt: 0
            });
            modifyLiquidityRouter.modifyLiquidity(key, range, ZERO_BYTES);
        }
        probe = new MathCanHookRouter(manager, hook);
        MockERC20(Currency.unwrap(currency0)).approve(address(probe), type(uint256).max);
    }

    function test_chtr10_hook_return_deltas_three_tick_crossings() public {
        PoolId id = key.toId();
        (uint160 priceBefore, int24 tickBefore,,) = manager.getSlot0(id);
        uint128 liqBefore = manager.getLiquidity(id);
        uint256 trader0Before = currency0.balanceOf(address(this));
        uint256 trader1Before = currency1.balanceOf(address(this));
        uint256 vault0Before = currency0.balanceOf(address(manager));
        uint256 vault1Before = currency1.balanceOf(address(manager));
        uint256 hook0Before = currency0.balanceOf(address(hook));
        uint256 hook1Before = currency1.balanceOf(address(hook));
        require(priceBefore == SQRT_PRICE_1_1 && tickBefore == 0 && liqBefore == 1e18, "initial state");
        SwapParams memory params = SwapParams({
            zeroForOne: true,
            amountSpecified: -int256(GROSS),
            sqrtPriceLimitX96: MIN_PRICE_LIMIT
        });
        vm.recordLogs();
        vm.startDebugTraceRecording();
        MathCanHookRouter.Observation memory obs = probe.execute(key, params);
        Vm.DebugStep[] memory steps = vm.stopAndReturnDebugTraceRecording();
        Vm.Log[] memory logs = vm.getRecordedLogs();
        require(steps.length > 0, "empty debugger trace");
        // Each manager TSTORE contributes two 32-byte words. Bound the extracted
        // manager-only buffer independently of the full Forge debug trace.
        bytes32[] memory writes = new bytes32[](64);
        uint256 n;
        for (uint256 i=0; i<steps.length; ++i) {
            if (steps[i].opcode != 0x5d || steps[i].contractAddr != address(manager)) continue;
            require(steps[i].stack.length >= 2, "missing TSTORE stack operands");
            require(n < 32, "too many manager TSTOREs");
            writes[2*n] = bytes32(steps[i].stack[0]);
            writes[2*n+1] = bytes32(steps[i].stack[1]);
            ++n;
        }
        assembly ("memory-safe") { mstore(writes, mul(n, 2)) }
        require(n >= 21, "missing transient writes");
        bytes32 sig = keccak256("Swap(bytes32,address,int128,int128,uint160,uint128,int24,uint24)");
        bool seen;
        int128 log0;
        int128 log1;
        uint160 logPrice;
        int24 logTick;
        uint128 logLiquidity;
        uint24 logFee;
        for (uint256 i = 0; i < logs.length; ++i) {
            if (logs[i].emitter != address(manager) || logs[i].topics.length < 3 || logs[i].topics[0]!=sig) continue;
            require(!seen && logs[i].topics[1] == PoolId.unwrap(id), "unexpected pool log");
            require(address(uint160(uint256(logs[i].topics[2]))) == address(probe), "unexpected swap sender");
            seen = true;
            (log0, log1, logPrice, logLiquidity, logTick, logFee) =
                abi.decode(logs[i].data, (int128, int128, uint160, uint128, int24, uint24));
        }
        require(seen && log0 == obs.poolDelta0 && log1 == obs.poolDelta1, "pool log/delta disagreement");
        require(logPrice == obs.finalPrice && logTick == obs.finalTick && logLiquidity == obs.finalLiquidity,
            "pool log/final slot mismatch");
        require(obs.finalLiquidity == 4e18 && obs.finalTick < -360 && obs.finalTick > -480,
            "expected three initialized tick crossings");
        require(obs.finalPrice < TickMath.getSqrtPriceAtTick(-360)
            && obs.finalPrice > TickMath.getSqrtPriceAtTick(-480), "wrong terminal price band");
        require(logFee == 3000 && obs.poolDelta0 == -int256(GROSS - 1e15), "wrong modified input");
        require(obs.hookDelta0 == 1e15 && obs.hookDelta1 == 5e12, "hook split wrong");
        require(obs.callerDelta0 == -int256(GROSS)
                && obs.callerDelta1 == obs.poolDelta1 - 5e12, "caller split wrong");
        require(obs.nonzeroAtSwap == 4 && obs.nonzeroAfterSettlement == 0, "transient count mismatch");
        require(manager.getNonzeroDeltaCount() == 0 && !manager.isUnlocked(), "unlock not settled");
        require(hook.beforeCalls() == 1 && hook.afterCalls() == 1, "hook callbacks missing");
        require(int256(currency0.balanceOf(address(this))) - int256(trader0Before) == obs.callerDelta0,
            "trader0 physical movement");
        require(int256(currency1.balanceOf(address(this))) - int256(trader1Before) == obs.callerDelta1,
            "trader1 physical movement");
        require(int256(currency0.balanceOf(address(hook))) - int256(hook0Before) == obs.hookDelta0,
            "hook0 physical movement");
        require(int256(currency1.balanceOf(address(hook))) - int256(hook1Before) == obs.hookDelta1,
            "hook1 physical movement");
        require(int256(currency0.balanceOf(address(manager))) - int256(vault0Before) == -obs.poolDelta0,
            "vault0 movement");
        require(int256(currency1.balanceOf(address(manager))) - int256(vault1Before) == -obs.poolDelta1,
            "vault1 movement");

        string memory k = "mathcan_chtr10";
        vm.serializeString(k, "schema", "mathcan.chtr10.hook-multitick.v1");
        vm.serializeString(k, "core_commit", CORE_COMMIT);
        vm.serializeAddress(k, "manager", address(manager));
        vm.serializeAddress(k, "router", address(probe));
        vm.serializeAddress(k, "hook", address(hook));
        vm.serializeAddress(k, "currency0", Currency.unwrap(currency0));
        vm.serializeAddress(k, "currency1", Currency.unwrap(currency1));
        vm.serializeBytes32(k, "manager_runtime_hash", address(manager).codehash);
        vm.serializeBytes32(k, "hook_runtime_hash", address(hook).codehash);
        vm.serializeBytes32(k, "pool_id", PoolId.unwrap(id));
        vm.serializeInt(k, "amount_specified", params.amountSpecified);
        vm.serializeInt(k, "before_specified", int256(hook.SPECIFIED_CUT()));
        vm.serializeInt(k, "before_unspecified", int256(hook.BEFORE_UNSPECIFIED()));
        vm.serializeInt(k, "after_unspecified", int256(hook.AFTER_UNSPECIFIED()));
        vm.serializeInt(k, "pool_delta0", obs.poolDelta0);
        vm.serializeInt(k, "pool_delta1", obs.poolDelta1);
        vm.serializeInt(k, "caller_delta0", obs.callerDelta0);
        vm.serializeInt(k, "caller_delta1", obs.callerDelta1);
        vm.serializeInt(k, "hook_delta0", obs.hookDelta0);
        vm.serializeInt(k, "hook_delta1", obs.hookDelta1);
        vm.serializeInt(k, "event_delta0", int256(log0));
        vm.serializeInt(k, "event_delta1", int256(log1));
        vm.serializeUint(k, "fee_pips", logFee);
        vm.serializeUint(k, "sqrt_price_before_x96", priceBefore);
        vm.serializeUint(k, "sqrt_price_after_x96", obs.finalPrice);
        vm.serializeInt(k, "tick_before", tickBefore);
        vm.serializeInt(k, "tick_after", obs.finalTick);
        vm.serializeUint(k, "liquidity_before", liqBefore);
        vm.serializeUint(k, "liquidity_after", obs.finalLiquidity);
        vm.serializeUint(k, "nonzero_at_swap", obs.nonzeroAtSwap);
        vm.serializeUint(k, "nonzero_after_settlement", obs.nonzeroAfterSettlement);
        vm.serializeUint(k, "trader0_before", trader0Before);
        vm.serializeUint(k, "trader1_before", trader1Before);
        vm.serializeUint(k, "trader0_after", currency0.balanceOf(address(this)));
        vm.serializeUint(k, "trader1_after", currency1.balanceOf(address(this)));
        vm.serializeUint(k, "hook0_before", hook0Before);
        vm.serializeUint(k, "hook1_before", hook1Before);
        vm.serializeUint(k, "hook0_after", currency0.balanceOf(address(hook)));
        vm.serializeUint(k, "hook1_after", currency1.balanceOf(address(hook)));
        vm.serializeUint(k, "vault0_before", vault0Before);
        vm.serializeUint(k, "vault1_before", vault1Before);
        vm.serializeUint(k, "vault0_after", currency0.balanceOf(address(manager)));
        vm.serializeUint(k, "vault1_after", currency1.balanceOf(address(manager)));
        vm.serializeUint(k, "debug_step_count", steps.length);
        vm.serializeUint(k, "manager_tstore_count", n);
        string memory json = vm.serializeBytes32(k, "manager_tstore_pairs", writes);
        vm.writeJson(json, ".forge-snapshots/mathcan_chtr10_hook_multitick.json");
    }
}
