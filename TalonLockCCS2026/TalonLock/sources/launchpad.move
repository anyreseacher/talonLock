module ctf::launchpad {
    use iota::transfer::{Receiving};
    use iota::coin::{Self, Coin};
    use iota::balance::{Self, Balance};
    use ctf::vesting::{create_strategy_not_for_coin, create_and_initialize_vester};
    use iota::dynamic_field as df;
    use iota::clock::{Self, Clock};
    use iota::table::{Self, Table};

    // Structure representing the amount of tokens vested to a user
    public struct AmountTo has store {
        user: address,       // Address of the user receiving vested tokens
        amount: u64,         // Amount of tokens vested to the user
    }

    public struct TimeFrame has copy, drop, store {
        time: u64,       // Time in seconds or appropriate units
        percentage: u8,  // Percentage of the total to be released at this time
    }


    // Structure to track user participation in the launchpad
    public struct Participation has store {
        user: address,     // Address of the participant
        amount: u64,       // Amount of tokens held by the participant
        amount_to_send: u64 // Amount of token to send to user
    }

    // Core structure representing the launchpad contract
    public struct Launchpad<phantom StakedToken, phantom TokenToPay> has key, store {        
        id: UID,                              
        raised_token: Balance<TokenToPay>,    // Token being raised
        conversion_rate_token: u8,            // Conversion rate between staked token and raised token
        total_staked: u64,                    // Total staked tokens
        start_time: u64,                      // Launchpad start time
        end_time: u64,                        // Launchpad end time
        total_allocation: u64,                // Total token allocation for the participants
        administrator: address,               // Admin address
        recipient_after_launch: address,      // Recipient of the raised funds after launch
        time_frame_claim_raised_amount: vector<TimeFrame>,  // Time frames for claiming raised amounts
        participants: Table<address, Participation>,  // List of participants
        is_active: bool,                      // Flag to check if the launchpad is active
        vesting_contract: Option<ID>, // Vesting contract created after launch
    }

    // <<<<<< Error codes >>>>>>
    const ERROR_LAUNCHPAD_NOT_ACTIVE: u64 = 1;          // Error code when trying to participate in an inactive Launchpad
    const ERROR_ALREADY_PARTICIPATED: u64 = 2;          // Error code when a user attempts to participate more than once
    const ERROR_INSUFFICIENT_FUNDS: u64 = 3;            // Error code when a user tries to stake without sufficient tokens
    const ERROR_LAUNCHPAD_CLOSED: u64 = 4;              // Error code when trying to close an already closed Launchpad
    const ERROR_NOT_ADMIN: u64 = 5;                     // Error code when non-admin tries to manage the Launchpad
    const ERROR_INVALID_TIME_FRAME_PARAMETERS: u64 = 7; // Error code for invalid time frame parameters (e.g., empty frames or zero percentages)
    
    // <<<<<< Launchpad functions >>>>>>

    // Function to create a new Launchpad
    public entry fun create_launchpad<StakedToken, TokenToPay>(
        conversion_rate_token: u8,           // Conversion rate for token to be raised
        total_allocation: u64,               // Total allocation of raised token
        start_time: u64,                     // Start time of the Launchpad
        end_time: u64,                       // End time of the Launchpad
        recipient_after_launch: address,     // Recipient of the raised tokens
        times: vector<u64>,                 // Vesting time frames
        percentages: vector<u8>,            // Vesting percentages
        ctx: &mut TxContext
    ) {
        let admin = tx_context::sender(ctx);
        // Ensure that times and percentages vectors are of equal length
        assert!(
            vector::length(&times) == vector::length(&percentages),
            ERROR_INVALID_TIME_FRAME_PARAMETERS
        );
        
        let mut time_frame_claim_raised_amount: vector<TimeFrame> = vector::empty();

        let len = vector::length(&times);
        let mut i = 0;
        while (i < len) {
            let time = *vector::borrow(&times, i);
            let percentage = *vector::borrow(&percentages, i);
            // Build the time frame and push to frames vector
            vector::push_back(
                &mut time_frame_claim_raised_amount,
                TimeFrame { time, percentage }
            );
            i = i + 1;
        };
        
        // Create a new Launchpad instance
        let launchpad = Launchpad<StakedToken, TokenToPay> {
            id: object::new(ctx),
            raised_token: balance::zero<TokenToPay>(),
            conversion_rate_token,
            total_staked: 0,
            start_time,
            end_time,
            total_allocation,
            administrator: admin,
            recipient_after_launch,
            time_frame_claim_raised_amount,
            participants: table::new<address, Participation>(ctx),
            is_active: true,   // Launchpad starts as active
            vesting_contract: option::none(), // Vesting contract will be created later
        };

        // Share the new Launchpad object
        transfer::share_object(launchpad);
    }

    // Register user participation in the launchpad
    public fun register_launchpad<StakedToken, TokenToPay>(
        launchpad: &mut Launchpad<StakedToken, TokenToPay>,    // Reference to the launchpad
        having_amount: Coin<StakedToken>,           // The amount the user is staking
        a_clock: &Clock,
        ctx: &mut TxContext                                    // Transaction context
    ): Coin<StakedToken> {
        let sender = tx_context::sender(ctx);

        // Ensure the launchpad is active and within the correct time frame
        assert!(launchpad.is_active, ERROR_LAUNCHPAD_NOT_ACTIVE);
        let current_time = clock::timestamp_ms(a_clock);
        assert!(
            current_time >= launchpad.start_time && current_time <= launchpad.end_time,
            ERROR_LAUNCHPAD_NOT_ACTIVE
        );

        // Ensure the user has not already participated
        assert!(
            !table::contains(&launchpad.participants, sender),
            ERROR_ALREADY_PARTICIPATED
        );

        let staked_value = coin::value(&having_amount);
        assert!(staked_value > 0, ERROR_INSUFFICIENT_FUNDS);

        // Add the participant to the participants table
        let participation = Participation {
            user: sender,
            amount: staked_value,   // Set the staked token amount here
            amount_to_send: (staked_value * (launchpad.conversion_rate_token as u64)), // Calculate the corresponding allocation
        };
        table::add(&mut launchpad.participants, sender, participation);

        // Update the total staked amount in the launchpad
        launchpad.total_staked = launchpad.total_staked + staked_value;
        having_amount
    }


    // User participation in the launchpad
    public entry fun participate_in_launchpad<StakedToken, TokenToPay>(
        launchpad: &mut Launchpad<StakedToken, TokenToPay>,
        token_to_pay: Receiving<Coin<TokenToPay>>,  // The amount the user wants to stake
        ctx: &mut TxContext
    ) {
        let sender = tx_context::sender(ctx);

        // Ensure the launchpad is active
        assert!(launchpad.is_active, ERROR_LAUNCHPAD_NOT_ACTIVE);

        // Ensure the user is registered (check if the user exists in the participants table)
        assert!(table::contains(&launchpad.participants, sender), ERROR_ALREADY_PARTICIPATED);

        // Borrow the participant from the table
        let participant = table::borrow_mut(&mut launchpad.participants, sender);

        // Ensure the user has not already participated fully (i.e., amount_to_send is not already set)
        assert!(participant.amount_to_send == 0, ERROR_ALREADY_PARTICIPATED);

        // Calculate the maximum amount the user is allowed to participate with
        let user_registered_amount = participant.amount;  // The amount the user registered with

        // Receive the tokens from the user (TokenToPay)
        let mut received_tokens = transfer::public_receive(&mut launchpad.id, token_to_pay);
        let received_value = coin::value(&received_tokens);
        assert!(received_value > 0, ERROR_INSUFFICIENT_FUNDS);

        // If the user sends more than they registered for, refund the extra
        let mut staked_value_to_use = received_value;
        if (received_value > user_registered_amount) {
            let extra_amount = received_value - user_registered_amount;

            // Refund the extra tokens
            let extra_tokens = coin::split(&mut received_tokens, extra_amount, ctx);
            transfer::public_transfer(extra_tokens, sender);

            staked_value_to_use = user_registered_amount;  // Only the registered amount will be used for calculation
        };

        // Calculate the user's share of the launchpad tokens using the conversion rate
        let staked_value_in_target_tokens = staked_value_to_use / (launchpad.conversion_rate_token as u64);

        // Calculate the user's share based on their staked amount and the launchpad total allocation
        let user_share = (staked_value_in_target_tokens * launchpad.total_allocation) / launchpad.total_staked;

        // Register the participant's `amount_to_send`
        participant.amount_to_send = user_share;

        // Update launchpad's total staked tokens (with the amount actually used)
        launchpad.total_staked = launchpad.total_staked + staked_value_to_use;

        // Add the used staked tokens to the raised token balance in the launchpad
        balance::join(&mut launchpad.raised_token, coin::into_balance(received_tokens));
    }


    // Close the launchpad
    public entry fun close_launchpad<StakedToken, TokenToPay>(
        launchpad: &mut Launchpad<StakedToken, TokenToPay>,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        let admin = tx_context::sender(ctx);
        // Get the current timestamp
        let current_time = clock::timestamp_ms(clock);
        // Ensure only the admin can close the launchpad
        assert!(admin == launchpad.administrator, ERROR_NOT_ADMIN);

        // Ensure the launchpad is still active
        assert!(launchpad.is_active && launchpad.end_time <= current_time, ERROR_LAUNCHPAD_CLOSED);

        // Set the launchpad as inactive
        launchpad.is_active = false;

        df::add(&mut launchpad.id, b"alredy_claimed", AmountTo {
                user: launchpad.recipient_after_launch,
                amount: 0
        });

        // The raised tokens will be gradually claimed by the recipient according to the time frames,
        // so we do not transfer any tokens at this point.
    }

    // Claim raised tokens according to the time frame
    public entry fun claim_raised_tokens<StakedToken, TokenToPay>(
        launchpad: &mut Launchpad<StakedToken, TokenToPay>,
        clock: &Clock,
        ctx: &mut TxContext
    ) {
        let recipient = tx_context::sender(ctx);
        
        // Ensure the sender is the recipient of the raised tokens
        assert!(recipient == launchpad.recipient_after_launch, ERROR_NOT_ADMIN);

        let amountTo: &mut AmountTo = df::borrow_mut(&mut launchpad.id, b"alredy_claimed");
        let claimed_amount = amountTo.amount;
        
        // Get the current timestamp
        let current_time = clock::timestamp_ms(clock);

        // Total claimable amount based on the time frames
        let mut total_claimable: u64 = 0;

        // Calculate the total amount the recipient can claim based on time frames
        let time_frames = &launchpad.time_frame_claim_raised_amount;
        let raised_amount = balance::value(&launchpad.raised_token);
        let num_frames = vector::length(time_frames);
        let mut i = 0;

        while (i < num_frames) {
            let frame = vector::borrow(time_frames, i);

            // Check if the current time has passed the frame's time, allowing claim
            if (current_time >= frame.time) {
                // Calculate the percentage of the raised tokens that can be claimed in this frame
                let claimable_in_frame = (frame.percentage as u64 * raised_amount) / 100;
                total_claimable = total_claimable + claimable_in_frame;
            } else {
                // Stop checking further frames since they are in the future
                break
            };
            i = i + 1;
        };

        // Ensure there are claimable funds
        assert!(total_claimable > claimed_amount && balance::value(&launchpad.raised_token) >= total_claimable - claimed_amount, ERROR_INSUFFICIENT_FUNDS);

        // Split the balance for the claimable amount
        let mut claimable_tokens_balance = balance::split(&mut launchpad.raised_token, (total_claimable - claimed_amount));
        let claimable_tokens = coin::take(&mut claimable_tokens_balance, (total_claimable - claimed_amount), ctx);

        amountTo.amount = total_claimable;
        // Transfer the claimable tokens to the recipient
        transfer::public_transfer(claimable_tokens, recipient);
        balance::destroy_zero(claimable_tokens_balance);  // Destroy any zero balances
    }


    // Create a vesting contract for the participants
    public entry fun create_the_vesting<StakedToken, TokenToPay, ClaimToken>(
        launchpad: &mut Launchpad<StakedToken, TokenToPay>,
        start_time: u64,
        duration_seconds: u64,
        receving_token : Receiving<Coin<ClaimToken>>,
        ctx: &mut TxContext
    ) {
        let admin = tx_context::sender(ctx);

        // Ensure only the admin can create the vesting contract
        assert!(admin == launchpad.administrator, ERROR_NOT_ADMIN);

        // Ensure the launchpad is not active anymore
        assert!(!launchpad.is_active, ERROR_LAUNCHPAD_NOT_ACTIVE);

        // Create vesting strategy
        let strategy = create_strategy_not_for_coin(
            1,  // Linear vesting strategy
            0,  // Amount will be calculated based on allocation
            ctx
        );


        let coin_to_vest = transfer::public_receive<Coin<ClaimToken>>(&mut launchpad.id, receving_token);
        
        // Initialize the vesting contract with the staked token balance
        let id = create_and_initialize_vester<ClaimToken, u64>(
            start_time,
            strategy,
            option::some(duration_seconds),
            option::none(),
            option::none(),
            coin_to_vest, 
            ctx
        );
        launchpad.vesting_contract = option::some(id);
        
    }
}