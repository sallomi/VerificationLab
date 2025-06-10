module vending_machine_checker(
    input logic clk,
    input logic rst,
    input logic [7:0] coin_in,
    input logic [1:0] button_in,
    input logic [7:0] change_out,
    input logic [1:0] beverage_out,
    input logic [7:0] credit,
    input logic [1:0] state
);

    // Assertion 1: When RESET is high, all outputs are zero and credit is zero.
    property reset_clears_all;
        @(posedge clk)
        rst |-> (change_out == 0 && beverage_out == 0 && credit == 0);
    endproperty
    assert property (reset_clears_all);

    // Assertion 2: When enough credit is present and a valid button is pressed, beverage_out will eventually pulse.
    property purchase_possible;
        @(posedge clk) disable iff (rst)
        ((credit >= 30 && button_in == 2'd1) || (credit >= 50 && button_in == 2'd2)) |-> ##[1:$] (beverage_out != 0);
    endproperty
    assert property (purchase_possible);

    // Assertion 3: If you try to buy with insufficient credit, beverage_out must remain zero.
    property cant_buy_with_insufficient_credit;
        @(posedge clk) disable iff (rst)
        ((button_in == 2'd1 && credit < 30) || (button_in == 2'd2 && credit < 50)) |-> (beverage_out == 0);
    endproperty
    assert property (cant_buy_with_insufficient_credit);

    // Assertion 4: After beverage is delivered, credit is decremented by the beverage price.
    property credit_decreased;
        @(posedge clk) disable iff (rst)
        ($rose(beverage_out)) |-> ($past(credit) == credit + (beverage_out == 2'd1 ? 30 : (beverage_out == 2'd2 ? 50 : 0)));
    endproperty
    assert property (credit_decreased);

    // Assertion 5: During DELIVER or CHANGE state, coin_in and button_in are always zero.
    property no_input_when_busy;
        @(posedge clk) disable iff (rst)
        ((state == 2'd1 || state == 2'd2)) |-> (coin_in == 0 && button_in == 0);
    endproperty
    assert property (no_input_when_busy);
// Assertion: When a valid coin is inserted, credit must increase by coin value
property coin_increases_credit;
    @(posedge clk) disable iff (rst)
    (coin_in == 8'd10 || coin_in == 8'd20 || coin_in == 8'd50 || coin_in == 8'd100 || coin_in == 8'd200)
    |=> (credit == $past(credit) + coin_in);
endproperty
assert property (coin_increases_credit);


endmodule
