`timescale 1ns/1ps

module tb_vending_machine;
    // Parameters for delays
    parameter N = 3;
    parameter M = 2;

    // Inputs and outputs
    logic clk, rst;
    logic [7:0] coin_in;
    logic [1:0] button_in;
    logic [7:0] change_out;
    logic [1:0] beverage_out;
    logic [7:0] credit;
    logic [1:0] state;

    // Instantiate the DUT
    vending_machine #(.N(N), .M(M)) dut (
        .clk(clk),
        .rst(rst),
        .coin_in(coin_in),
        .button_in(button_in),
        .change_out(change_out),
        .beverage_out(beverage_out),
        .credit(credit),   // <-- new connection!
        .state(state)      // <-- new connection!
    );

    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk; // 10ns clock period

    // Stimulus
    initial begin
        // Initialize
        rst = 1; coin_in = 0; button_in = 0;
        #20;
        rst = 0;

        // Insert 20c (invalid for water), press water (should ignore)
        coin_in = 8'd20; #10; coin_in = 0; #10;
        button_in = 2'd0; #10; button_in = 0; #50;

        // Insert 10c (credit = 30c), press water (should deliver)
        coin_in = 8'd10; #10; coin_in = 0; #10;
        button_in = 2'd0; #10; button_in = 0; #50;

        // Wait for delivery + possible change
        #100;

        // Insert 2€ (200c), buy soda (should deliver and have change)
        coin_in = 8'd200; #10; coin_in = 0; #10;
        button_in = 2'd1; #10; button_in = 0; #100;

        // Try to buy water with 150c left, should deliver
        button_in = 2'd0; #10; button_in = 0; #100;

        // Try to buy soda with remaining credit < 50c, should ignore
        button_in = 2'd1; #10; button_in = 0; #100;

        // Wait for possible change
        #100;

        $stop;
    end

    // Optionally, monitor outputs
    initial begin
        $monitor("Time=%0t | coin_in=%0d, button_in=%0d, beverage_out=%0d, change_out=%0d, credit(internal)=%0d",
            $time, coin_in, button_in, beverage_out, change_out, dut.credit);
    end

endmodule

