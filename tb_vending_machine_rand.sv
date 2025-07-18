`timescale 1ns/1ps
class Generator;
    mailbox mbx;
    int num_transactions;
    function new(mailbox mbx_, int num_trans);
        mbx = mbx_;
        num_transactions = num_trans;
    endfunction

    task run();
        // Generate random transactions and put them in the mailbox
        for (int i = 0; i < num_transactions; i++) begin
            // Create and send a transaction
            // mbx.put(transaction); // Fill this as needed
        end
    endtask
endclass

class Driver;
    mailbox mbx;
    function new(mailbox mbx_);
        mbx = mbx_;
    endfunction

    task run();
        // Get transactions from mailbox and drive them to DUT
        // while (1) begin
        //   mbx.get(transaction); // Fill this as needed
        //   // drive signals
        // end
    endtask
endclass

module tb_vending_machine_rand;
    parameter N = 3;
    parameter M = 2;

    // Inputs/Outputs
    logic clk, rst;
    logic [7:0] coin_in;
    logic [1:0] button_in;
    logic [7:0] change_out;
    logic [1:0] beverage_out;
    logic [7:0] credit;
    logic [1:0] state;

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

    // Clock
    initial clk = 0;
    always #5 clk = ~clk;

    // Transaction class
    // ... (unchanged, all your classes as before) ...

    // Testbench environment
    mailbox mbx = new();
    Generator gen;
    Driver drv;

    // **CORRECT DUMP BLOCK AT TIME 0**
    initial begin
        clk = 0;
        rst = 1;
        coin_in = 0;
        button_in = 0;
        $dumpfile("mywaves.vcd");
        $dumpvars(0, tb_vending_machine_rand);
    end

    // MAIN SIMULATION (after dump is enabled and everything is initialized)
    initial begin
        #20;
        rst = 0;
        // Instantiate classes
        gen = new(mbx, 25); // number of transactions
        drv = new(mbx);
        // Start generator and driver in parallel
        fork
            gen.run();
            drv.run();
        join_none

        #2000; // run enough time for all transactions
        $stop;
    end

    // Optionally, monitor outputs
    initial begin
        $monitor("Time=%0t | coin_in=%0d, button_in=%0d, beverage_out=%0d, change_out=%0d, credit(internal)=%0d",
            $time, coin_in, button_in, beverage_out, change_out, dut.credit);
    end

endmodule

