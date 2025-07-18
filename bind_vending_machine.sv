bind vending_machine vending_machine_checker checker_inst(
    .clk(clk),
    .rst(rst),
    .coin_in(coin_in),
    .button_in(button_in),
    .change_out(change_out),
    .beverage_out(beverage_out),
    .credit(credit),
    .state(state)
);

