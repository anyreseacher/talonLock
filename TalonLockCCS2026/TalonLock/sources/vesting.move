#[allow(unused_assignment)]
module ctf::vesting {
    use iota::transfer::{Receiving};
    use iota::coin::{Self, Coin};
    use iota::pay;
    use iota::balance::{Self, Balance};
    use iota::dynamic_field as df;
    use iota::clock::{Self, Clock};

    // <<<<<<<<<<<<<<<<<<<<<<<< Error codes <<<<<<<<<<<<<<<<<<<<<<<<
    // Error codes for assertion failures throughout the contract
    const ERROR_INVALID_DURATION: u64 = 1;              // Error code for invalid vesting duration (e.g., duration <= 0)
    const ERROR_INSUFFICIENT_FUNDS: u64 = 2;            // Error code when there are insufficient funds to release or collect
    const ERROR_TOO_EARLY_RELEASE: u64 = 3;             // Error code for attempting to release funds before the vesting period or a time frame has passed
    const ERROR_NOT_ADMIN: u64 = 4;                     // Error code when a non-administrator tries to perform restricted actions (e.g., adding supply or collecting coins)
    const ERROR_INVALID_STRATEGY: u64 = 5;              // Error code for using an invalid or unsupported vesting strategy
    const ERROR_INVALID_LENGTH: u64 = 6;                // Error code for mismatched vector lengths (e.g., between time frames and percentages)
    const ERROR_INVALID_VESTING_PARAMETERS: u64 = 7;    // Error code when both duration and time frames are missing, making the vesting configuration invalid
    const ERROR_INVALID_TIME_FRAME_PARAMETERS: u64 = 8; // Error code for invalid time frame parameters (e.g., empty frames or zero percentages)
    const ERROR_VESTING_NOT_ENDED : u64 = 9;            // Error code for attempting to collect non-vested funds before the vesting period has fully ended


    public struct TimeFrame has copy, drop, store {
        time: u64,       // Time in seconds or appropriate units
        percentage: u8,  // Percentage of the total to be released at this time
    }

    // Structure representing the amount of tokens vested to a user
    public struct AmountTo has store {
        user: address,       // Address of the user receiving vested tokens
        amount: u64,         // Amount of tokens vested to the user
    }

    public struct StrategyType<phantom Type>  has key, store {
         id: UID,  
         id_strategy: u8,           // Strategy type: 1 for linea equal distribution, 2 for dynamic key-value distribution // Strategy type: 3 for special coin distribution, user having x amount of coin B can receive coins
         amount_each: u64           // Amount for each user if strategy type is 1
    }

    // Structure representing the core of the vesting contract
    public struct Vesting<phantom Asset, StrategyType> has key, store {
        id: UID,                   // Unique identifier for the vesting contract
        coin: Balance<Asset>,      // Balance of tokens in the contract
        supply: u64,               // Amount of tokens provided to this vester
        start: u64,                // Vesting start timestamp
        administrator: address,    // Address of the administrator for the vesting contract
        total_vested: u64,         // Total amount of tokens vested so far
        strategy: StrategyType, 
        duration: Option<u64>,             // Vesting duration in seconds
        time_frames: Option<vector<TimeFrame>>  // time , percentage
    }

    // Creates a vesting strategy object with specific rules (not for coin-based strategies)
    public fun create_strategy_not_for_coin(
        id_strategy: u8,                 // Strategy type (1 for linear, 2 for dynamic key-value distribution)
        amount_each: u64,                // Amount to be vested per user
        ctx: &mut TxContext              // Transaction context
    ) : StrategyType<u64>  {
        // Ensure the strategy type is valid (either 1 or 2)
        assert!(id_strategy == 1 || id_strategy == 2, ERROR_INVALID_STRATEGY);

        // For strategy type 1, ensure amount_each is valid
        if (id_strategy == 1) {
            assert!(amount_each > 0, ERROR_INVALID_STRATEGY);
        };

        // Create a `StrategyType` with the `VestingStrategy` UID
        let strategy_type_with_vesting = StrategyType<u64> {
            id: object::new(ctx),
            id_strategy: id_strategy,         // Use the provided strategy type
            amount_each: amount_each          // Use the provided amount for each user
        };
        strategy_type_with_vesting
    }

    // Creates a vesting strategy object for a specific coin
    public fun create_strategy_for_coin<BaseCoin>(
        id_strategy: u8,                 // Strategy type (3 for coin-based strategies)
        amount_each: u64,                // Amount to be vested per user
        ctx: &mut TxContext              // Transaction context
    ): StrategyType<BaseCoin> {
        // Ensure the strategy type is valid (must be 3 for coin-based strategies)
        assert!(id_strategy == 3, ERROR_INVALID_STRATEGY);

        // Create a `StrategyType` with the `VestingStrategyForCoin` UID
        let strategy_type_with_vesting_for_coin = StrategyType<BaseCoin> {
            id: object::new(ctx),
            id_strategy: id_strategy,         // Use the provided strategy type (3)
            amount_each: amount_each          // Use the provided amount for each user
        };

        strategy_type_with_vesting_for_coin
    }

    #[allow(lint(share_owned))]
    public entry fun create_vester_and_share<Asset, Type>(
        _start_timestamp: u64,                // Vesting start time
        _strategy: StrategyType<Type>,        // Vesting strategy
        _duration_seconds: Option<u64>,       // Vesting duration (optional)
        _times: Option<vector<u64>>,         // Vesting time frames (optional)
        _percentages: Option<vector<u8>>,    // Vesting percentages (optional)
        ctx: &mut TxContext                  // Transaction context
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
        // Share the vesting object
        transfer::share_object(vesting);
        return id
    }

    // Function to create a new vesting contract with time_frames built from parameters
    public fun create_vester<Asset, Type>(
        start_timestamp: u64,                // Vesting start time
        strategy: StrategyType<Type>,        // Vesting strategy
        duration_seconds: Option<u64>,       // Vesting duration (optional)
        times_: Option<vector<u64>>,         // Vesting time frames (optional)
        percentages_: Option<vector<u8>>,    // Vesting percentages (optional)
        ctx: &mut TxContext                  // Transaction context
    ) : Vesting<Asset, StrategyType<Type>> {
        // Ensure that at least one of duration_seconds or time_frames is provided
        assert!(
            option::is_some(&duration_seconds) || option::is_some(&times_),
            ERROR_INVALID_VESTING_PARAMETERS
        );

        if (option::is_some(&duration_seconds)) {
            assert!(*option::borrow(&duration_seconds) > 0, ERROR_INVALID_DURATION);
        };

        // Build the time_frames vector if times_ and percentages_ are provided
        let mut time_frames: Option<vector<TimeFrame>> = option::none();

        if (option::is_some(&times_) && option::is_some(&percentages_)) {
            let times = option::borrow(&times_);
            let percentages = option::borrow(&percentages_);

            // Ensure that times and percentages vectors are of equal length
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
                // Build the time frame and push to frames vector
                vector::push_back(
                    &mut frames,
                    TimeFrame { time, percentage }
                );
                i = i + 1;
            };
            time_frames = option::some(frames);
            assert!(validate_time_frames(time_frames), ERROR_INVALID_TIME_FRAME_PARAMETERS);
            
        };

        // Create a new vesting object
        let vesting = Vesting<Asset, StrategyType<Type>> {
            id: object::new(ctx),                             // Assign a unique ID to the vesting contract
            coin: coin::into_balance(coin::zero<Asset>(ctx)), // Initialize balance to zero
            supply: 0,                                        // No tokens supply for vesting at the start
            start: start_timestamp,                           // Set the vesting start timestamp
            duration: duration_seconds,                       // Set the vesting duration (can be None)
            administrator: tx_context::sender(ctx),           // Set the sender as the administrator
            total_vested: 0,                                  // Total amount vested, initially set to zero
            strategy,                                         // Apply the vesting strategy
            time_frames                                       // Set the time frame (can be None if not provided)
        };
        vesting
    }


    // Initializes the vesting contract with funds to be vested
    public fun initialize_vester<Asset, Type>(
        _vester: &mut Vesting<Asset, StrategyType<Type>>,     // Vesting contract to be initialized
        _to_vest: Receiving<Coin<Asset>>,           // Coins to be vested
        ctx: &mut TxContext                        // Transaction context
    ) {
        let sender = tx_context::sender(ctx);   // Get the sender's address

        // Ensure only the administrator can add funds to the vesting contract
        assert!(sender == _vester.administrator, ERROR_NOT_ADMIN);

        // Receive the coins into the vesting contract
        let coin_to_vest = transfer::public_receive(&mut _vester.id, _to_vest);
        assert!(coin::value(&coin_to_vest) > 0, 0);
        _vester.supply = _vester.supply + coin::value(&coin_to_vest);
        balance::join(&mut _vester.coin, coin::into_balance(coin_to_vest)); // Add the coins to the balance
    }

    #[allow(lint(share_owned))]
    // Initializes the vesting contract with funds to be vested
    public fun create_and_initialize_vester<Asset, Type>(
        _start_timestamp: u64,                // Vesting start time
        _strategy: StrategyType<Type>,        // Vesting strategy
        _duration_seconds: Option<u64>,       // Vesting duration (optional)
        _times: Option<vector<u64>>,         // Vesting time frames (optional)
        _percentages: Option<vector<u8>>,    // Vesting percentages (optional)_to_vest: Coin<Asset>,                      // Coins to be vested
        _to_vest: Coin<Asset>,           // Coins to be vested
        ctx: &mut TxContext                        // Transaction context
    ) : ID {
        let sender = tx_context::sender(ctx);   // Get the sender's address

        // Create the vesting contract
        let mut _vester = create_vester<Asset, Type>(
            _start_timestamp,
            _strategy,
            _duration_seconds,
            _times,
            _percentages,
            ctx
        );

        // Ensure only the administrator can add funds to the vesting contract
        assert!(sender == _vester.administrator, ERROR_NOT_ADMIN);

        assert!(coin::value(&_to_vest) > 0, 0);
        _vester.supply = _vester.supply + coin::value(&_to_vest);
        balance::join(&mut _vester.coin, coin::into_balance(_to_vest)); // Add the coins to the balance
        
        let id = object::id(&_vester);
        transfer::share_object(_vester);

        return id
    }


    
    
    // Releases vested tokens to the user based on the schedule
    public entry fun release_coins<Asset>(
        _vester: &mut Vesting<Asset, StrategyType<u64>>, 
        _clock: &Clock,
        ctx: &mut TxContext
    ) {
        let sender = tx_context::sender(ctx);             // Get the sender's address
        let current_time = clock::timestamp_ms(_clock);     // Get the current timestamp in milliseconds
        let strategy = &mut _vester.strategy;              // Reference the vesting strategy

        // Ensure the current time is after the vesting start time
        assert!(current_time >= _vester.start, ERROR_TOO_EARLY_RELEASE);

        // Ensure the correct coin-based strategy is used (strategy.id_strategy should be 1 or 2)
        assert!(strategy.id_strategy < 3, ERROR_INVALID_STRATEGY);

        let mut releasable: u64 = 0;
        let mut released: u64 = 0;

        if (option::is_some(&_vester.duration)) {
            // Calculate released and releasable amounts based on the strategy
            (released, releasable) = get_linear_releasable_amount(
                strategy, &mut _vester.id, sender, current_time, _vester.start, *option::borrow(&_vester.duration)
            );
        } else {
            released = get_released_amount_to_user(&mut _vester.id, sender);
            releasable = get_frame_base_releasable_amount(
                get_amount_for_user(strategy, sender),
                released,
                _vester.start,
                (current_time - _vester.start),
                *option::borrow(&_vester.duration),
                option::is_some(&_vester.duration),
                *option::borrow(&_vester.time_frames)
            );
        };

        // Ensure there are releasable funds and the contract has sufficient balance
        assert!(releasable > 0 && balance::value(&_vester.coin) >= releasable, ERROR_INSUFFICIENT_FUNDS);

        // Send the releasable amount to the user and update the vesting contract
        send_to_user_and_update_vester(_vester, sender, releasable, released, ctx);
    }


    // Releases tokens using a coin-based vesting strategy
    public entry fun release_coins_by_coinbase<Asset, BaseCoin>(
        vester: &mut Vesting<Asset, StrategyType<BaseCoin>>, // Vesting contract with an asset and strategy
        clock: &Clock,                                      // Clock to track time and calculate vesting period
        coinList: vector<Coin<BaseCoin>>,                   // List of coins to be vested
        ctx: &mut TxContext                                 // Transaction context
    ) {
        let mut coinB = coin::zero<BaseCoin>(ctx);
        
        // Join multiple coins into one to avoid counting 
        pay::join_vec<BaseCoin>(&mut coinB, coinList);
        let strategy = &vester.strategy;
        let sender = tx_context::sender(ctx);
        let current_time = clock::timestamp_ms(clock);

        // Ensure the current time is greater than or equal to the vesting start time
        assert!(current_time >= vester.start, ERROR_TOO_EARLY_RELEASE);

        // Ensure that the strategy being used is the correct coin-based strategy (id_strategy == 3)
        assert!(strategy.id_strategy == 3, ERROR_INVALID_STRATEGY);

        let mut released = 0;   

        // Check if the sender has previously received any vested tokens
        if (df::exists_(&vester.id, sender)) {
            let vesterTo: &mut AmountTo = df::borrow_mut(&mut vester.id, sender);
            released = vesterTo.amount;
        };

        // Calculate the time that has passed since the vesting started
        let time_elapsed = current_time - vester.start;
        
        
        // Get the total amount available in the BaseCoin instance created earlier
        let mut my_total_amount = coin::value(&coinB);

        // Check if the sender's record exists in the strategy mapping
        if (!df::exists_(&strategy.id, sender)) {
            df::add(&mut vester.strategy.id, sender, AmountTo {
                user: sender,
                amount: my_total_amount
            });
        } else {
            let vesterTo: &mut AmountTo = df::borrow_mut(&mut vester.strategy.id, sender);
            // Update the total amount with the sender's amount from the record
            my_total_amount = vesterTo.amount;
        };

        let releasable = get_frame_base_releasable_amount(
            my_total_amount,
            released,
            vester.start,
            time_elapsed,
            *option::borrow(&vester.duration),
            option::is_some(&vester.duration),
            *option::borrow(&vester.time_frames)
        );
        // Ensure that there are releasable funds and that the contract has enough balance to release them
        assert!(releasable > 0 && balance::value(&vester.coin) > releasable, ERROR_INSUFFICIENT_FUNDS);

        // Send the releasable tokens to the user and update the vesting contract with the released amount
        send_to_user_and_update_vester(vester, sender, releasable, released, ctx);

        // Transfer the entire coin to the sender
        transfer::public_transfer(coinB, sender);
    }


    // Adds more coins to the vesting contract's supply
    public entry fun add_supply_of_coin<Asset, Type>(
        vester: &mut Vesting<Asset, StrategyType<Type>>,       // Vesting contract to add supply to
        to_vest: Receiving<Coin<Asset>>,            // Coins to be added
        ctx: &mut TxContext                         // Transaction context
    ) {
        let sender = tx_context::sender(ctx);  // Get the address of the sender

        // Ensure only the administrator can add supply
        assert!(sender == vester.administrator, ERROR_NOT_ADMIN);

        // Receive the coins and add them to the contract's balance
        let coin_to_vest = transfer::public_receive(&mut vester.id, to_vest);
        assert!(coin::value(&coin_to_vest) > 0, 0);
        vester.supply = vester.supply + coin::value(&coin_to_vest);
        balance::join(&mut vester.coin, coin::into_balance(coin_to_vest));
    }

    // Collects non-vested coins after the vesting period ends
    #[allow(lint(self_transfer))]
    public entry fun collect_not_vested_coins<Asset, Type>(
        vester: &mut Vesting<Asset, StrategyType<Type>>, 
        clock: &Clock, 
        ctx: &mut TxContext
    ) {
        let sender = tx_context::sender(ctx);  // Get the address of the sender
        let current_time = clock::timestamp_ms(clock); // Get the current timestamp
        
        // Ensure only the administrator can collect and the vesting period has ended
        assert!(sender == vester.administrator, ERROR_NOT_ADMIN);

        assert!(has_vesting_ended(vester, current_time), ERROR_VESTING_NOT_ENDED);

        let balanceCoin = balance::value(&vester.coin);  // Get the remaining balance

        // Ensure the contract has remaining funds
        assert!(balanceCoin > 0, ERROR_INSUFFICIENT_FUNDS);

        // Split the contract's balance to collect the remaining coins
        let mut balance_vest = balance::split(&mut vester.coin, balanceCoin);
        let coin_vest = coin::take(&mut balance_vest, balanceCoin, ctx);  // Take the coins
        transfer::public_transfer(coin_vest, sender);  // Transfer them to the administrator
        balance::destroy_zero(balance_vest);  // Destroy any zero balances
    }

    // Allocates custom amounts for each user using a dynamic strategy
    public entry fun set_allocate_amount_per_user<Asset, Type>(
        vester: &mut Vesting<Asset, StrategyType<Type>>,           // Vesting contract
        users: vector<address>,                          // List of users
        amounts: vector<u64>,                            // Corresponding amounts for each user
        ctx: &mut TxContext                              // Transaction context
    ) {
        let sender = tx_context::sender(ctx);  // Get the address of the sender

        let mut _strategy = &mut vester.strategy;
        // Ensure only the administrator can allocate amounts
        assert!(sender == vester.administrator, ERROR_NOT_ADMIN);

        // Ensure that the strategy is dynamic (strategy.id_strategy == 2)
        assert!(_strategy.id_strategy == 2, ERROR_INVALID_STRATEGY);

        // Ensure the lengths of the users and amounts vectors match
        assert!(vector::length(&users) == vector::length(&amounts), ERROR_INVALID_LENGTH);

        let length = vector::length(&users);  // Get the number of users
        let mut i = 0;                        // Initialize loop counter

        // Iterate over the list of users to allocate amounts
        while (i < length) {
            let user = vector::borrow(&users, i);        // Get user at index `i`
            let amount = vector::borrow(&amounts, i);    // Get corresponding amount

            // If no record exists for the user, create a new one
            if (!df::exists_(&_strategy.id, *user)) {
                df::add(&mut _strategy.id, *user, AmountTo {
                    user: *user,
                    amount: *amount
                });
            } else {
                // If a record exists, update the amount
                let vesterTo: &mut AmountTo = df::borrow_mut(&mut _strategy.id, *user);
                vesterTo.amount = vesterTo.amount + *amount;
            };

            i = i + 1;  // Increment loop counter
        }
    }

    // <<<<<<<Internal functions >>>>>>
    // Function to validate and order time frames
    fun validate_time_frames(
        time_frames_option: Option<vector<TimeFrame>>
    ): bool {
        // Check if time_frames_option is None, return false if so
        if (!option::is_some(&time_frames_option)) {
            return true
        };

        // Extract the time_frames vector from the Option
        let time_frames = option::borrow(&time_frames_option);

        // Ensure the vector is not empty
        let length = vector::length(time_frames);
        if (length == 0) {
            return true
        };

        let mut total_percentage: u8 = 0;
        let mut previous_time: u64 = 0;

        // Iterate over the time_frames vector to validate each TimeFrame
        let mut i = 0;
        while (i < length) {
            let frame = vector::borrow(time_frames, i);

            // Ensure that no percentage is 0
            if (frame.percentage == 0) {
                return false
            };

            // Sum up the percentages
            total_percentage = total_percentage + frame.percentage;

            // Ensure the time frames are ordered by time (ascending order)
            if (i > 0 && frame.time <= previous_time) {
                return false
            };

            // Update previous_time for the next iteration
            previous_time = frame.time;
            i = i + 1;
        };

        // Ensure the total percentage sums to exactly 100
        if (total_percentage != 100) {
            return false
        };

        true
    }

    // Function to calculate releasable amount
    fun get_frame_base_releasable_amount(
        my_total_amount: u64,        // Total amount to be vested
        released_amount: u64,        // Amount already released
        start_time: u64,             // Start Time
        time_elapsed: u64,           // Time passed since vesting started
        vesting_duration: u64,       // Total vesting duration (used in duration-based strategy)
        is_duration_based: bool,     // Boolean to choose the strategy
        time_frames: vector<TimeFrame> // Time frames for time-frame-based strategy
    ): u64 {
        // Declare the variable for the releasable amount
        let mut releasable: u64 = 0;

        // Duration-based vesting strategy
        if (is_duration_based) {
            // If the total vesting duration is completed, release all remaining tokens
            if (time_elapsed >= vesting_duration) {
                releasable = my_total_amount - released_amount;
            } else {
                // Release tokens proportionally based on the time elapsed
                releasable = (my_total_amount * time_elapsed) / vesting_duration - released_amount;
            }
        } else {
            // Time-frame-based vesting strategy
            let mut total_percentage: u8 = 0;
            let mut all_frames_passed: bool = true;

            // Iterate through each time frame in the vector
            let length = vector::length<TimeFrame>(&time_frames);
            let mut i = 0;

            while (i < length) {
                let frame = vector::borrow<TimeFrame>(&time_frames, i);

                // Check if the time frame has been passed
                if (time_elapsed >= (start_time - frame.time)) {
                    // Add the percentage corresponding to this time frame
                    total_percentage = total_percentage + frame.percentage;
                } else {
                    all_frames_passed = false;
                    break // Exit the loop if a future time frame is found
                };

                i = i + 1;
            };

            // If all frames have passed, release all remaining tokens
            if (all_frames_passed) {
                releasable = my_total_amount - released_amount;
            } else {
                // Calculate releasable amount based on the total percentage of passed time frames
                releasable = (my_total_amount * (total_percentage as u64)) / 100 - released_amount;
            };
        };
        // Return the amount of tokens that are releasable
        releasable
    }

    // Calculates the amount vested for a specific user
    #[allow(unused_mut_ref)]
    fun get_amount_for_user<Type>(
        _vester_strategy: &mut StrategyType<Type>, 
        _user: address
    ) : u64 {        
        // If strategy type is 1, use the fixed amount per user
        if (_vester_strategy.id_strategy == 1) {
            return _vester_strategy.amount_each
        };
        // If strategy type is 2 and dynamic field exists for the sender, retrieve the specific amount
        if (_vester_strategy.id_strategy == 2 && df::exists_(&_vester_strategy.id, _user)) { 
            let amountR : &AmountTo = df::borrow(&mut _vester_strategy.id, _user); 
            return amountR.amount
        };
        return 0
    }

    // Get previously received vested tokens by user
    fun get_released_amount_to_user (
        _vester_id: &mut UID, 
        _user: address
    ): u64 {
        if (df::exists_(_vester_id, _user)) {
            let vesterTo: &mut AmountTo = df::borrow_mut(_vester_id, _user);
            return vesterTo.amount
        };
        return 0
    }

    // Calculates the releasable and already released amounts based on the vesting schedule
    fun get_linear_releasable_amount<Type>(
        _strategy: &mut StrategyType<Type>, 
        _id: &mut UID, 
        _user: address, 
        _current_time: u64,
        _start: u64, 
        _duration: u64
    ) : (u64, u64) {
        let released = get_released_amount_to_user(_id, _user);   // Amount already released to the sender

        // Calculate the time elapsed since the vesting started
        let time_elapsed = _current_time - _start;
        let releasable;  // Amount releasable based on vesting schedule
        let my_total_amount = get_amount_for_user(_strategy, _user);
        
        // If vesting duration is complete, all remaining tokens are releasable
        if (time_elapsed >= _duration) {
            releasable = my_total_amount - released;
        } else {
            // Otherwise, calculate the releasable amount based on time elapsed
            releasable = my_total_amount * time_elapsed / _duration - released;
        };

        (released, releasable)
    }

    // Sends releasable tokens to the user and updates the vesting record
    fun send_to_user_and_update_vester<Asset, StrategyType>(
        _vester: &mut Vesting<Asset, StrategyType>, 
        _sender: address,
        _releasable: u64,
        _released: u64,
        ctx: &mut TxContext
    ) {
        // Split the contract's balance to release the releasable amount
        let mut balance_vest = balance::split(&mut _vester.coin, _releasable);
        let coin_vest = coin::take(&mut balance_vest, _releasable, ctx);  // Take releasable coins
        transfer::public_transfer(coin_vest, _sender);  // Transfer the coins to the user
        balance::destroy_zero(balance_vest);  // Destroy any remaining balance if zero

        // Update or create the vesting record for the user
        if (!df::exists_(&_vester.id, _sender)) {
            df::add(&mut _vester.id, _sender, AmountTo {
                user: _sender,
                amount: _releasable + _released   // Add to the total released amount
            });
        } else {
            let vesterTo: &mut AmountTo = df::borrow_mut(&mut _vester.id, _sender);
            vesterTo.amount = _releasable + _released;  // Update released amount
        };

        _vester.total_vested = _vester.total_vested + _releasable;  // Update the total vested amount
    }

    // Helper function to check if the vesting period has ended
    fun has_vesting_ended<Asset, Type>(
        _vester: &Vesting<Asset, StrategyType<Type>>,
        _current_time: u64
    ): bool {
        // If the vesting strategy is duration-based, check if the duration has passed
        if (option::is_some(&_vester.duration)) {
            let duration = *option::borrow(&_vester.duration);
            let end_time = _vester.start + duration;
            return _current_time >= end_time  // Vesting has ended if current time exceeds the end time
        };

        // If the vesting strategy is time-frame-based, check if all time frames have passed
        if (option::is_some(&_vester.time_frames)) {
            let time_frames = option::borrow(&_vester.time_frames);
            let len = vector::length(time_frames);

            // Check the last time frame
            if (len > 0) {
                let last_time_frame = vector::borrow(time_frames, len - 1);
                return _current_time >= last_time_frame.time  // Vesting ends after the last time frame
            }
        };

        false // Return false if the vesting period hasn't ended
    }
    // <<<< Consider the option were we can mint token instead of geting in advance >>>>
}
