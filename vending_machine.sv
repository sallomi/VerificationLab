module vending_machine #(
    parameter N = 3,  // Delivery wait cycles
    parameter M = 2   // Change return wait cycles
)(
    input  logic clk,
    input  logic rst,
    input  logic [7:0] coin_in,       // 10, 20, 50, 100, 200
    input  logic [1:0] button_in,     // 1 = Water, 2 = Soda
    output logic [7:0] change_out,
    output logic [1:0] beverage_out,
    output logic [7:0] credit,
    output logic [1:0] state
);

    // Internal registers for outputs
    typedef enum logic [1:0] {IDLE, DELIVER, CHANGE} state_t;
    state_t state_reg, next_state;

    logic [7:0] credit_reg, next_credit;
    logic [7:0] price;
    logic [7:0] next_change;
    logic [1:0] next_beverage;
    logic [$clog2(N+1)-1:0] deliver_counter;
    logic [$clog2(M+1)-1:0] change_counter;

    // Beverage price logic
    always_comb begin
        case (button_in)
            2'd1: price = 8'd30;   // Water
            2'd2: price = 8'd50;   // Soda
            default: price = 8'd0;
        endcase
    end

    // State machine
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            state_reg <= IDLE;
            credit_reg <= 0;
            change_out <= 0;
            beverage_out <= 0;
            deliver_counter <= 0;
            change_counter <= 0;
        end else begin
            state_reg <= next_state;
            credit_reg <= next_credit;
            change_out <= next_change;
            beverage_out <= next_beverage;
            if (state_reg == DELIVER)
                deliver_counter <= deliver_counter + 1;
            else
                deliver_counter <= 0;
            if (state_reg == CHANGE)
                change_counter <= change_counter + 1;
            else
                change_counter <= 0;
        end
    end

    // Next state logic
    always_comb begin
        next_state = state_reg;
        next_credit = credit_reg;
        next_change = 0;
        next_beverage = 0;

        case (state_reg)
            IDLE: begin
                next_beverage = 0;
                next_change = 0;
                // Accept coins
                if (coin_in == 8'd10 || coin_in == 8'd20 || coin_in == 8'd50 || coin_in == 8'd100 || coin_in == 8'd200) begin
                   // next_credit = credit_reg + coin_in;
// Fault: Do nothing, credit stays the same
                end
                // Accept beverage selection only if enough credit
                else if ((button_in == 2'd1 && credit_reg >= 8'd30) || (button_in == 2'd2 && credit_reg >= 8'd50)) begin
                    next_state = DELIVER;
                    next_credit = credit_reg - price;
                    next_beverage = button_in;
                end
            end
            DELIVER: begin
                next_beverage = beverage_out;
                next_credit = credit_reg;
                next_change = 0;
                // Wait N cycles
                if (deliver_counter == N-1) begin
                    // After delivery, check if remaining credit < 30
                    if (credit_reg < 8'd30) begin
                        next_state = CHANGE;
                        next_change = credit_reg;
                        next_credit = 0;
                    end else begin
                        next_state = IDLE;
                    end
                end
            end
            CHANGE: begin
                next_beverage = 0;
                next_change = change_out;
                // Wait M cycles to return change
                if (change_counter == M-1) begin
                    next_state = IDLE;
                end
            end
        endcase
    end

    // Assign outputs to internal registers
    assign credit = credit_reg;
    assign state  = state_reg;

endmodule
