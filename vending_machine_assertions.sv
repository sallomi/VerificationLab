// Assertion 1: When RESET is high, all outputs are zero and credit is zero.
always @(posedge clk) 
    rst |-> (change_out == 0 && beverage_out == 0 && dut.credit == 0);

// Assertion 2: When enough credit is present and a valid button is pressed, beverage_out will eventually pulse.
property purchase_possible;
    @(posedge clk) disable iff (rst)
    ((credit >= 30 && button_in == 2'd1) || (credit >= 50 && button_in == 2'd2)) |-> s_eventually (beverage_out != 0);
endproperty
assert property (purchase_possible);

// Assertion 3: If you try to buy with insufficient credit, beverage_out must remain zero.
always @(posedge clk) disable iff (rst)
    ((button_in == 2'd1 && credit < 30) || (button_in == 2'd2 && credit < 50)) |-> beverage_out == 0;

// Assertion 4: After beverage is delivered, credit is decremented by the beverage price.
property credit_decreased;
    @(posedge clk) disable iff (rst)
    ($rose(beverage_out)) |-> ($past(credit) == credit + (beverage_out == 2'd1 ? 30 : (beverage_out == 2'd2 ? 50 : 0)));
endproperty
assert property (credit_decreased);

// Assertion 5: During DELIVER or CHANGE state, beverage_out can pulse once, but coin_in and button_in are always zero.
always @(posedge clk) disable iff (rst)
    ((dut.state == dut.DELIVER || dut.state == dut.CHANGE)) |-> (coin_in == 0 && button_in == 0);
// Assertion: When a valid coin is inserted, credit must increase by coin value
property coin_increases_credit;
    @(posedge clk) disable iff (rst)
    (coin_in == 8'd10 || coin_in == 8'd20 || coin_in == 8'd50 || coin_in == 8'd100 || coin_in == 8'd200)
    |=> (credit == $past(credit) + coin_in);
endproperty
assert property (coin_increases_credit);

