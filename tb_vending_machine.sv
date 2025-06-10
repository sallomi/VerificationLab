module tb_vending_machine;

    // Parameters for delivery/change cycles
    parameter N = 3;  // Beverage delivery cycles
    parameter M = 2;  // Change return cycles

    // DUT I/O
    logic clk, rst;
    logic [7:0] coin_in;
    logic [1:0] button_in;
    logic [7:0] change_out;
    logic [1:0] beverage_out;

    // Instantiate DUT
    vending_machine #(.N(N), .M(M)) dut (
        .clk(clk),
        .rst(rst),
        .coin_in(coin_in),
        .button_in(button_in),
        .change_out(change_out),
        .beverage_out(beverage_out)
    );

    // Clock generator: 10ns period
    always #5 clk = ~clk;

    initial begin
        // Initialize signals
        clk = 0; rst = 1;
        coin_in = 0;
        button_in = 0;
        #20;               // Reset for a few cycles
        rst = 0;

        // TEST CASE 1: Insert five 10c coins, buy soda
        @(negedge clk); coin_in = 8'd10;
        @(negedge clk); coin_in = 8'd10;
        @(negedge clk); coin_in = 8'd10;
        @(negedge clk); coin_in = 8'd10;
        @(negedge clk); coin_in = 8'd10;
        @(negedge clk); coin_in = 0;
        @(negedge clk); button_in = 2'd2; // Soda
        @(negedge clk); button_in = 0;

        repeat (N + M + 2) @(negedge clk);

        // TEST CASE 2: Insert 1 Euro, buy soda, expect change
        @(negedge clk); coin_in = 8'd100; // 1 Euro
        @(negedge clk); coin_in = 0;
        @(negedge clk); button_in = 2'd2; // Soda
        @(negedge clk); button_in = 0;

        repeat (N + M + 2) @(negedge clk);

        // TEST CASE 3: Insert 2 Euro, buy soda, expect large change
        @(negedge clk); coin_in = 8'd200; // 2 Euro
        @(negedge clk); coin_in = 0;
        @(negedge clk); button_in = 2'd2; // Soda
        @(negedge clk); button_in = 0;

        repeat (N + M + 2) @(negedge clk);

        // TEST CASE 4: Insert coins for water (20c + 10c), buy water
        @(negedge clk); coin_in = 8'd20;
        @(negedge clk); coin_in = 8'd10;
        @(negedge clk); coin_in = 0;
        @(negedge clk); button_in = 2'd1; // Water
        @(negedge clk); button_in = 0;

        repeat (N + M + 2) @(negedge clk);

        // TEST CASE 5: Insert 10c, try to buy soda (should fail: not enough credit)
        @(negedge clk); coin_in = 8'd10;
        @(negedge clk); coin_in = 0;
        @(negedge clk); button_in = 2'd2; // Try soda with only 10c
        @(negedge clk); button_in = 0;

        repeat (5) @(negedge clk);

        $display("Testbench finished.");
        $stop;
    end

    // Monitor signals for debugging
    initial begin
        $monitor("[%0t] rst=%b coin_in=%d button_in=%d credit=%d beverage_out=%d change_out=%d state=%0d",
            $time, rst, coin_in, button_in, dut.credit, beverage_out, change_out, dut.state);
    end
// ADD BIND STATEMENT HERE:
    bind vending_machine vending_machine_checker checker_inst (
        .clk(clk),
        .rst(rst),
        .coin_in(coin_in),
        .button_in(button_in),
        .change_out(change_out),
        .beverage_out(beverage_out),
        .credit(credit),
        .state(state)
    );

endmodule
