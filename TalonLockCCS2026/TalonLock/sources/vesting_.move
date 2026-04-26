#[allow(unused_assignment)]
module ctf::vesting {
    use iota::transfer::{Receiving};
    use iota::coin::{Self, Coin};
    use iota::pay;
    use iota::balance::{Self, Balance};
    use iota::dynamic_field as df;
    use iota::clock::{Self, Clock};

    const ERROR_INVALID_DURATION: u64 = 1;
    const ERROR_INSUFFICIENT_FUNDS: u64 = 2;
    const ERROR_TOO_EARLY_RELEASE: u64 = 3;
    const ERROR_NOT_ADMIN: u64 = 4;
    const ERROR_INVALID_STRATEGY: u64 = 5;
    const ERROR_INVALID_LENGTH: u64 = 6;
    const ERROR_INVALID_VESTING_PARAMETERS: u64 = 7;
    const ERROR_INVALID_TIME_FRAME_PARAMETERS: u64 = 8;
    const ERROR_VESTING_NOT_ENDED : u64 = 9;

    public struct TimeFrame has copy, drop, store {
        time: u64,
        percentage: u8,
    }

    public struct AmountTo has store {
        user: address,
        amount: u64,
    }

    public struct LockedProofKey has copy, drop, store {
        user: address,
    }

    public struct StrategyType<phantom Type> has key, store {
         id: UID,
         id_strategy: u8,
         amount_each: u64
    }

    public struct Vesting<phantom Asset, StrategyType> has key, store {
        id: UID,
        coin: Balance<Asset>,
        supply: u64,
        start: u64,
        administrator: address,
        total_vested: u64,
        strategy: StrategyType,
        duration: Option<u64>,
        time_frames: Option<vector<TimeFrame>>
    }

    public fun create_strategy_not_for_coin(
        id_strategy: u8,
        amount_each: u64,
        ctx: &mut TxContext
    ) : StrategyType<u64>  {
        assert!(id_strategy == 1 || id_strategy == 2, ERROR_INVALID_STRATEGY);
        if (id_strategy == 1) {
            assert!(amount_each > 0, ERROR_INVALID_STRATEGY);
        };

        StrategyType<u64> {
            id: object::new(ctx),
            id_strategy,
            amount_each
        }
    }

    public fun create_strategy_for_coin<BaseCoin>(
        id_strategy: u8,
        amount_each: u64,
        ctx: &mut TxContext
    ): StrategyType<BaseCoin> {
        assert!(id_strategy == 3, ERROR_INVALID_STRATEGY);

        StrategyType<BaseCoin> {
            id: object::new(ctx),
            id_strategy,
            amount_each
        }
    }

    #[allow(lint(share_owned))]
    public entry fun create_vester_and_share<Asset, Type>(
        _start_timestamp: u64,
        _strategy: StrategyType<Type>,
        _duration_seconds: Option<u64>,
        _times: Option<vector<u64>>,
        _percentages: Option<vector<u8>>,
        ctx: &mut TxContext
    ) : ID {
        let vesting = create_vester<Asset, Type>(
            _start_timestamp,
            _strategy,
            _duration_seconds,
            _times,
            _percentages,
            ctx
        );
        let id = object::id(&vesting);
        transfer::share_object(vesting);
        id
    }

    public fun create_vester<Asset, Type>(
        start_timestamp: u64,
        strategy: StrategyType<Type>,
        duration_seconds: Option<u64>,
        times_: Option<vector<u64>>,
        percentages_: Option<vector<u8>>,
        ctx: &mut TxContext
    ) : Vesting<Asset, StrategyType<Type>> {
        assert!(
            option::is_some(&duration_seconds) || option::is_some(&times_),
            ERROR_INVALID_VESTING_PARAMETERS
        );

        if (option::is_some(&duration_seconds)) {
            assert!(*option::borrow(&duration_seconds) > 0, ERROR_INVALID_DURATION);
        };

        let mut time_frames: Option<vector<TimeFrame>> = option::none();

        if (option::is_some(&times_) && option::is_some(&percentages_)) {
            let times = option::borrow(&times_);
            let percentages = option::borrow(&percentages_);
            assert!(
                vector::length(times) == vector::length(percentages),
                ERROR_INVALID_TIME_FRAME_PARAMETERS
            );

            let mut frames: vector<TimeFrame> = vector::empty();
            let len = vector::length(times);
            let mut i = 0;
            while (i < len) {
                let time = *vector::borrow(times, i);
                let percentage = *vector::borrow(percentages, i);
                vector::push_back(&mut frames, TimeFrame { time, percentage });
                i = i + 1;
            };
            time_frames = option::some(frames);
            assert!(validate_time_frames(time_frames), ERROR_INVALID_TIME_FRAME_PARAMETERS);
        };

        Vesting<Asset, StrategyType<Type>> {
            id: object::new(ctx),
            coin: coin::into_balance(coin::zero<Asset>(ctx)),
            supply: 0,
            start: start_timestamp,
            duration: duration_seconds,
            administrator: tx_context::sender(ctx),
            total_vested: 0,
            strategy,
            time_frames
        }
    }

    public fun initialize_vester<Asset, Type>(
        _vester: &mut Vesting<Asset, StrategyType<Type>>,
        _to_vest: Receiving<Coin<Asset>>,
        ctx: &mut TxContext
    ) {
        let sender = tx_context::sender(ctx);
        assert!(sender == _vester.administrator, ERROR_NOT_ADMIN);

        let coin_to_vest = transfer::public_receive(&mut _vester.id, _to_vest);
        assert!(coin::value(&coin_to_vest) > 0, ERROR_INSUFFICIENT_FUNDS);
        _vester.supply = _vester.supply + coin::value(&coin_to_vest);
        balance::join(&mut _vester.coin, coin::into_balance(coin_to_vest));
    }

    #[allow(lint(share_owned))]
    public fun create_and_initialize_vester<Asset, Type>(
        _start_timestamp: u64,
        _strategy: StrategyType<Type>,
        _duration_seconds: Option<u64>,
        _times: Option<vector<u64>>,
        _percentages: Option<vector<u8>>,
        _to_vest: Coin<Asset>,
        ctx: &mut TxContext
    ) : ID {
        let sender = tx_context::sender(ctx);

        let mut _vester = create_vester<Asset, Type>(
            _start_timestamp,
            _strategy,
            _duration_seconds,
            _times,
            _percentages,
            ctx
        );

        assert!(sender == _vester.administrator, ERROR_NOT_ADMIN);
        assert!(coin::value(&_to_vest) > 0, ERROR_INSUFFICIENT_FUNDS);

        _vester.supply = _vester.supply + coin::value(&_to_vest);
        balance::join(&mut _vester.coin, coin::into_balance(_to_vest));

        let id = object::id(&_vester);
        transfer::share_object(_vester);
        id
    }

    #[allow(lint(share_owned))]
    public fun create_and_initialize_vester_with_allocations<Asset>(
        _start_timestamp: u64,
        _strategy: StrategyType<u64>,
        _duration_seconds: Option<u64>,
        _times: Option<vector<u64>>,
        _percentages: Option<vector<u8>>,
        _to_vest: Coin<Asset>,
        users: vector<address>,
        amounts: vector<u64>,
        ctx: &mut TxContext
    ) : ID {
        let sender = tx_context::sender(ctx);

        let mut _vester = create_vester<Asset, u64>(
            _start_timestamp,
            _strategy,
            _duration_seconds,
            _times,
            _percentages,
            ctx
        );

        assert!(sender == _vester.administrator, ERROR_NOT_ADMIN);
        assert!(coin::value(&_to_vest) > 0, ERROR_INSUFFICIENT_FUNDS);

        _vester.supply = _vester.supply + coin::value(&_to_vest);
        balance::join(&mut _vester.coin, coin::into_balance(_to_vest));
        set_allocate_amount_per_user_internal(&mut _vester.strategy, users, amounts);

        let id = object::id(&_vester);
        transfer::share_object(_vester);
        id
    }

    public entry fun release_coins<Asset>(
        _vester: &mut Vesting<Asset, StrategyType<u64>>,
        _clock: &Clock,
        ctx: &mut TxContext
    ) {
        let sender = tx_context::sender(ctx);
        let current_time = clock::timestamp_ms(_clock);
        let strategy = &mut _vester.strategy;

        assert!(current_time >= _vester.start, ERROR_TOO_EARLY_RELEASE);
        assert!(strategy.id_strategy < 3, ERROR_INVALID_STRATEGY);

        let mut releasable: u64 = 0;
        let mut released: u64 = 0;

        if (option::is_some(&_vester.duration)) {
            (released, releasable) = get_linear_releasable_amount(
                strategy,
                &mut _vester.id,
                sender,
                current_time,
                _vester.start,
                *option::borrow(&_vester.duration)
            );
        } else {
            released = get_released_amount_to_user(&mut _vester.id, sender);
            releasable = get_frame_base_releasable_amount(
                get_amount_for_user(strategy, sender),
                released,
                _vester.start,
                current_time - _vester.start,
                current_time,
                0,
                false,
                *option::borrow(&_vester.time_frames)
            );
        };

        assert!(
            releasable > 0 && balance::value(&_vester.coin) >= releasable,
            ERROR_INSUFFICIENT_FUNDS
        );

        send_to_user_and_update_vester(_vester, sender, releasable, released, ctx);
    }

    public entry fun release_coins_by_coinbase<Asset, BaseCoin>(
        vester: &mut Vesting<Asset, StrategyType<BaseCoin>>,
        clock: &Clock,
        coinList: vector<Coin<BaseCoin>>,
        ctx: &mut TxContext
    ) {
        let mut coinB = coin::zero<BaseCoin>(ctx);
        pay::join_vec<BaseCoin>(&mut coinB, coinList);

        let sender = tx_context::sender(ctx);
        let current_time = clock::timestamp_ms(clock);

        assert!(current_time >= vester.start, ERROR_TOO_EARLY_RELEASE);
        assert!(vester.strategy.id_strategy == 3, ERROR_INVALID_STRATEGY);

        let released = get_released_amount_to_user(&mut vester.id, sender);
        let time_elapsed = current_time - vester.start;

        let entitlement: u64;
        if (!df::exists_(&vester.strategy.id, sender)) {
            let proof_value = coin::value(&coinB);
            assert!(proof_value > 0, ERROR_INSUFFICIENT_FUNDS);

            df::add(&mut vester.strategy.id, sender, AmountTo {
                user: sender,
                amount: proof_value
            });

            df::add(
                &mut vester.strategy.id,
                LockedProofKey { user: sender },
                coin::into_balance(coinB)
            );

            entitlement = proof_value;
        } else {
            assert!(coin::value(&coinB) == 0, ERROR_INVALID_STRATEGY);
            coin::destroy_zero(coinB);
            let rec: &AmountTo = df::borrow(&vester.strategy.id, sender);
            entitlement = rec.amount;
        };

        let releasable = if (option::is_some(&vester.duration)) {
            get_frame_base_releasable_amount(
                entitlement,
                released,
                vester.start,
                time_elapsed,
                current_time,
                *option::borrow(&vester.duration),
                true,
                vector::empty<TimeFrame>()
            )
        } else {
            get_frame_base_releasable_amount(
                entitlement,
                released,
                vester.start,
                time_elapsed,
                current_time,
                0,
                false,
                *option::borrow(&vester.time_frames)
            )
        };

        assert!(
            releasable > 0 && balance::value(&vester.coin) >= releasable,
            ERROR_INSUFFICIENT_FUNDS
        );

        send_to_user_and_update_vester(vester, sender, releasable, released, ctx);
    }

    public entry fun add_supply_of_coin<Asset, Type>(
        vester: &mut Vesting<Asset, StrategyType<Type>>,
        to_vest: Receiving<Coin<Asset>>,
        ctx: &mut TxContext
    ) {
        let sender = tx_context::sender(ctx);
        assert!(sender == vester.administrator, ERROR_NOT_ADMIN);

        let coin_to_vest = transfer::public_receive(&mut vester.id, to_vest);
        assert!(coin::value(&coin_to_vest) > 0, ERROR_INSUFFICIENT_FUNDS);
        vester.supply = vester.supply + coin::value(&coin_to_vest);
        balance::join(&mut vester.coin, coin::into_balance(coin_to_vest));
    }

    #[allow(lint(self_transfer))]
    public entry fun collect_not_vested_coins<Asset, Type>(
        vester: &mut Vesting<Asset, StrategyType<Type>>,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        let sender = tx_context::sender(ctx);
        let current_time = clock::timestamp_ms(clock);

        assert!(sender == vester.administrator, ERROR_NOT_ADMIN);
        assert!(has_vesting_ended(vester, current_time), ERROR_VESTING_NOT_ENDED);

        let balanceCoin = balance::value(&vester.coin);
        assert!(balanceCoin > 0, ERROR_INSUFFICIENT_FUNDS);

        let mut balance_vest = balance::split(&mut vester.coin, balanceCoin);
        let coin_vest = coin::take(&mut balance_vest, balanceCoin, ctx);
        transfer::public_transfer(coin_vest, sender);
        balance::destroy_zero(balance_vest);
    }

    public entry fun set_allocate_amount_per_user<Asset, Type>(
        vester: &mut Vesting<Asset, StrategyType<Type>>,
        users: vector<address>,
        amounts: vector<u64>,
        ctx: &mut TxContext
    ) {
        let sender = tx_context::sender(ctx);
        let _strategy = &mut vester.strategy;

        assert!(sender == vester.administrator, ERROR_NOT_ADMIN);
        assert!(_strategy.id_strategy == 2, ERROR_INVALID_STRATEGY);

        set_allocate_amount_per_user_internal(_strategy, users, amounts);
    }

    fun set_allocate_amount_per_user_internal<Type>(
        _strategy: &mut StrategyType<Type>,
        users: vector<address>,
        amounts: vector<u64>
    ) {
        assert!(vector::length(&users) == vector::length(&amounts), ERROR_INVALID_LENGTH);

        let length = vector::length(&users);
        let mut i = 0;

        while (i < length) {
            let user = *vector::borrow(&users, i);
            let amount = *vector::borrow(&amounts, i);

            if (!df::exists_(&_strategy.id, user)) {
                df::add(&mut _strategy.id, user, AmountTo {
                    user,
                    amount
                });
            } else {
                let vesterTo: &mut AmountTo = df::borrow_mut(&mut _strategy.id, user);
                vesterTo.amount = amount;
            };

            i = i + 1;
        }
    }

    fun validate_time_frames(time_frames_option: Option<vector<TimeFrame>>): bool {
        if (!option::is_some(&time_frames_option)) {
            return true
        };

        let time_frames = option::borrow(&time_frames_option);
        let length = vector::length(time_frames);
        if (length == 0) {
            return false
        };

        let mut total_percentage: u8 = 0;
        let mut previous_time: u64 = 0;
        let mut i = 0;

        while (i < length) {
            let frame = vector::borrow(time_frames, i);

            if (frame.percentage == 0) {
                return false
            };

            total_percentage = total_percentage + frame.percentage;

            if (i > 0 && frame.time <= previous_time) {
                return false
            };

            previous_time = frame.time;
            i = i + 1;
        };

        total_percentage == 100
    }

    fun get_frame_base_releasable_amount(
        my_total_amount: u64,
        released_amount: u64,
        start_time: u64,
        time_elapsed: u64,
        current_time: u64,
        vesting_duration: u64,
        is_duration_based: bool,
        time_frames: vector<TimeFrame>
    ): u64 {
        let mut releasable: u64 = 0;

        if (is_duration_based) {
            if (time_elapsed >= vesting_duration) {
                releasable = my_total_amount - released_amount;
            } else {
                releasable =
                    (my_total_amount * time_elapsed) / vesting_duration - released_amount;
            }
        } else {
            let mut total_percentage: u8 = 0;
            let mut all_frames_passed: bool = true;
            let length = vector::length<TimeFrame>(&time_frames);
            let mut i = 0;

            while (i < length) {
                let frame = vector::borrow<TimeFrame>(&time_frames, i);
                if (current_time >= frame.time) {
                    total_percentage = total_percentage + frame.percentage;
                } else {
                    all_frames_passed = false;
                    break
                };
                i = i + 1;
            };

            if (all_frames_passed) {
                releasable = my_total_amount - released_amount;
            } else {
                releasable =
                    (my_total_amount * (total_percentage as u64)) / 100 - released_amount;
            };
        };
        releasable
    }

    #[allow(unused_mut_ref)]
    fun get_amount_for_user<Type>(
        _vester_strategy: &mut StrategyType<Type>,
        _user: address
    ) : u64 {
        if (_vester_strategy.id_strategy == 1) {
            return _vester_strategy.amount_each
        };
        if (_vester_strategy.id_strategy == 2 && df::exists_(&_vester_strategy.id, _user)) {
            let amountR: &AmountTo = df::borrow(&_vester_strategy.id, _user);
            return amountR.amount
        };
        0
    }

    fun get_released_amount_to_user(
        _vester_id: &mut UID,
        _user: address
    ): u64 {
        if (df::exists_(_vester_id, _user)) {
            let vesterTo: &AmountTo = df::borrow(_vester_id, _user);
            return vesterTo.amount
        };
        0
    }

    fun get_linear_releasable_amount<Type>(
        _strategy: &mut StrategyType<Type>,
        _id: &mut UID,
        _user: address,
        _current_time: u64,
        _start: u64,
        _duration: u64
    ) : (u64, u64) {
        let released = get_released_amount_to_user(_id, _user);
        let time_elapsed = _current_time - _start;
        let my_total_amount = get_amount_for_user(_strategy, _user);
        let releasable;

        if (time_elapsed >= _duration) {
            releasable = my_total_amount - released;
        } else {
            releasable = my_total_amount * time_elapsed / _duration - released;
        };

        (released, releasable)
    }

    fun send_to_user_and_update_vester<Asset, StrategyType>(
        _vester: &mut Vesting<Asset, StrategyType>,
        _sender: address,
        _releasable: u64,
        _released: u64,
        ctx: &mut TxContext
    ) {
        let mut balance_vest = balance::split(&mut _vester.coin, _releasable);
        let coin_vest = coin::take(&mut balance_vest, _releasable, ctx);
        transfer::public_transfer(coin_vest, _sender);
        balance::destroy_zero(balance_vest);

        if (!df::exists_(&_vester.id, _sender)) {
            df::add(&mut _vester.id, _sender, AmountTo {
                user: _sender,
                amount: _releasable + _released
            });
        } else {
            let vesterTo: &mut AmountTo = df::borrow_mut(&mut _vester.id, _sender);
            vesterTo.amount = _releasable + _released;
        };

        _vester.total_vested = _vester.total_vested + _releasable;
    }

    fun has_vesting_ended<Asset, Type>(
        _vester: &Vesting<Asset, StrategyType<Type>>,
        _current_time: u64
    ): bool {
        if (option::is_some(&_vester.duration)) {
            let duration = *option::borrow(&_vester.duration);
            return _current_time >= _vester.start + duration
        };

        if (option::is_some(&_vester.time_frames)) {
            let time_frames = option::borrow(&_vester.time_frames);
            let len = vector::length(time_frames);
            if (len > 0) {
                let last_time_frame = vector::borrow(time_frames, len - 1);
                return _current_time >= last_time_frame.time
            };
            return true
        };

        true
    }
}
