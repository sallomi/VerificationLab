module tb_vending_machine_rand;

    // Parameters
    parameter N = 3;
    parameter M = 2;

    // Inputs and outputs
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
        .beverage_out(beverage_out),
        .credit(credit),
        .state(state)
    );

    // Valid coin values
    localparam int NUM_COINS = 5;
    logic [7:0] coin_values [NUM_COINS-1:0] = '{8'd10, 8'd20, 8'd50, 8'd100, 8'd200};

    // Valid button values
    localparam int NUM_BUTTONS = 2;
    logic [1:0] button_values [NUM_BUTTONS-1:0] = '{2'd1, 2'd2}; // 1=water, 2=soda

    // Clock generation
    always #5 clk = ~clk;

    // Random transaction generator task
    task automatic rand_transaction();
        int steps = $urandom_range(10, 30); // Number of random steps in a transaction
        for (int i = 0; i < steps; i++) begin
            // Only operate if not busy (i.e., not delivering/returning change)
            if (dut.state == 0) begin // IDLE
                // Randomly choose to insert coin or press button or do nothing
                int action = $urandom_range(0, 2);
                if (action == 0) begin
                    // Insert a random coin
                    int idx = $urandom_range(0, NUM_COINS-1);
                    coin_in = coin_values[idx];
                    button_in = 0;
                    $display("[%0t] Insert coin: %0d", $time, coin_in);
                end else if (action == 1) begin
                    // Press a random button
                    int idx = $urandom_range(0, NUM_BUTTONS-1);
                    coin_in = 0;
                    button_in = button_values[idx];
                    $display("[%0t] Press button: %0d", $time, button_in);
                end else begin
                    // Do nothing
                    coin_in = 0;
                    button_in = 0;
                end
            end else begin
                // If busy, do nothing
                coin_in = 0;
                button_in = 0;
            end
            @(negedge clk);
        end
        // End with no input
        coin_in = 0;
        button_in = 0;
    endtask

bind vending_machine vending_machine_checker checker_inst(
    .clk(clk),
    .rst(rst),
    .coin_in(coin_in),
    .button_in(button_in),
    .change_out(change_out),
    .beverage_out(beverage_out),
    .credit(dut.credit),
    .state(dut.state)
);


    initial begin
        clk = 0; rst = 1; coin_in = 0; button_in = 0;
        #20; // Hold reset
        rst = 0;
        @(negedge clk);

        // Run several random transactions
        repeat (5) begin
            rand_transaction();
            repeat (N + M + 2) @(negedge clk); // Wait for possible delivery/change
        end

        $display("Randomized testbench finished.");
        $stop;
    end

    // Monitor for debugging
    initial begin
        $monitor("[%0t] rst=%b coin_in=%d button_in=%d credit=%d beverage_out=%d change_out=%d state=%0d",
            $time, rst, coin_in, button_in, dut.credit, beverage_out, change_out, dut.state);
    end

endmodule
