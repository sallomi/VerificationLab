module vending_machine_assertions
    #(parameter N = 3)
    (
        input logic clk,
        input logic rst,
        input logic [7:0] coin_in,
        input logic [1:0] button_in,
        input logic [7:0] change_out,
        input logic [1:0] beverage_out,
        input logic [7:0] credit // If you want to check credit directly, otherwise connect dut.credit in bind/checker
    );

// 1. Valid Coin Acceptance
assert property (@(posedge clk)
    (coin_in !== 0) |-> (coin_in == 8'd10 || coin_in == 8'd20 ||
                         coin_in == 8'd50 || coin_in == 8'd100 || coin_in == 8'd200)
);

// 2. Beverage Delivery Only with Sufficient Credit
assert property (@(posedge clk)
    (button_in == 2'd0 && beverage_out == 2'd1) |-> (credit + 8'd30 >= 8'd30)
);

assert property (@(posedge clk)
    (button_in == 2'd1 && beverage_out == 2'd2) |-> (credit + 8'd50 >= 8'd50)
);

// 3. No Inputs Accepted During Delivery
property p_delivery_no_input;
    @(posedge clk)
    disable iff (rst)
    (beverage_out != 2'd0) |-> ##[1:N] (coin_in == 0 && button_in == 0);
endproperty
assert property (p_delivery_no_input);

// 4. Change Returned Only When Credit < 30c
assert property (@(posedge clk)
    (change_out !== 8'd0) |-> (beverage_out != 2'd0 && credit < 8'd30)
);

// 5. No Beverage Delivered Without Button Press
assert property (@(posedge clk)
    (beverage_out != 2'd0) |-> (button_in != 2'd0 || button_in != 2'd1)
);

endmodule

