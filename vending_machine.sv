module vending_machine #(
    parameter N = 3,
    parameter M = 2
)(
    input  logic        clk,
    input  logic        rst,
    input  logic [7:0]  coin_in,
    input  logic [1:0]  button_in,
    output logic [7:0]  change_out,
    output logic [1:0]  beverage_out,
    output logic [7:0]  credit,
    output logic [1:0]  state
);

    // Internal registers
    logic [7:0] credit_reg, next_credit;
    logic [1:0] state_reg, next_state;
    logic [7:0] change_reg, next_change_reg;
    logic [1:0] beverage_reg, next_beverage_reg;
    logic [$clog2(N+1)-1:0] dispense_cnt;
    logic [$clog2(M+1)-1:0] change_cnt;

    // Coin values allowed
    localparam COIN_10  = 8'd10;
    localparam COIN_20  = 8'd20;
    localparam COIN_50  = 8'd50;
    localparam COIN_100 = 8'd100;
    localparam COIN_200 = 8'd200;

    // Beverage prices
    localparam PRICE_WATER = 8'd30;
    localparam PRICE_SODA  = 8'd50;

    // State encoding
    typedef enum logic [2:0] {
        IDLE         = 3'd0,
        ACCEPT_COINS = 3'd1,
        DISPENSE     = 3'd2,
        CHANGE       = 3'd3
    } state_t;

    // FSM state and next state
    state_t state_val, next_state_val;

    // Accept coin?
    function logic is_valid_coin(input logic [7:0] coin);
        return (coin == COIN_10) || (coin == COIN_20) ||
               (coin == COIN_50) || (coin == COIN_100) ||
               (coin == COIN_200);
    endfunction

    // Synchronous FSM
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            state_reg      <= IDLE;
            credit_reg     <= 0;
            change_reg     <= 0;
            beverage_reg   <= 0;
            dispense_cnt   <= 0;
            change_cnt     <= 0;
        end else begin
            state_reg      <= next_state;
            credit_reg     <= next_credit;
            change_reg     <= next_change_reg;
            beverage_reg   <= next_beverage_reg;
            if (state_reg == DISPENSE)
                dispense_cnt <= dispense_cnt + 1;
            else
                dispense_cnt <= 0;
            if (state_reg == CHANGE)
                change_cnt <= change_cnt + 1;
            else
                change_cnt <= 0;
        end
    end

    // Combinational next state logic
    always_comb begin
        next_beverage_reg = beverage_reg;
        next_change_reg = change_reg;
        next_state      = state_reg;
        next_credit     = credit_reg;
        change_out      = 0;
        beverage_out    = 0;

        unique case (state_reg)
            IDLE: begin
                if (is_valid_coin(coin_in))
                    next_state = ACCEPT_COINS;
                else if ((button_in == 2'd1 && credit_reg >= PRICE_WATER) ||
                         (button_in == 2'd2 && credit_reg >= PRICE_SODA))
                    next_state = DISPENSE;
                else
                    next_state = IDLE;
            end

            ACCEPT_COINS: begin
                if (is_valid_coin(coin_in))
                    next_credit = credit_reg + coin_in;
                // After coin, check if button pressed and enough credit
                if ((button_in == 2'd1 && next_credit >= PRICE_WATER) ||
                    (button_in == 2'd2 && next_credit >= PRICE_SODA))
                    next_state = DISPENSE;
                else
                    next_state = ACCEPT_COINS;
            end

            DISPENSE: begin
                if (dispense_cnt == N-1) begin
                    if (button_in == 2'd1) begin
                        next_credit = credit_reg - PRICE_WATER;
                        next_beverage_reg = 2'd1;
                    end else if (button_in == 2'd2) begin
                        next_credit = credit_reg - PRICE_SODA;
                        next_beverage_reg = 2'd2;
                    end
                    // If remaining credit < min price, go to CHANGE
                    if (next_credit < PRICE_WATER && next_credit < PRICE_SODA && next_credit != 0) begin
                        next_change_reg = next_credit;
                        next_credit = 0;
                        next_state = CHANGE;
                    end else
                        next_state = IDLE;
                end else
                    next_state = DISPENSE;
            end

            CHANGE: begin
                if (change_cnt == M-1) begin
                    change_out = change_reg;
                    next_state = IDLE;
                end else
                    next_state = CHANGE;
            end

            default: begin
                next_state = IDLE;
            end
        endcase

        // Outputs
        if (state_reg == DISPENSE && dispense_cnt == N-1)
            beverage_out = beverage_reg;
        if (state_reg == CHANGE && change_cnt == M-1)
            change_out = change_reg;
    end

    // Output assignments
    assign credit = credit_reg;
    assign state  = state_reg;

endmodule

