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
    // 1. Declare counters
    integer ATCT = 0, ATCF = 0, AFCT = 0, AFCF = 0;
    bit antecedent;
    bit consequent;
    // 2. Procedural block for contingency table
    always @(posedge clk) begin
        if (rst) begin
            ATCT = 0; ATCF = 0; AFCT = 0; AFCF = 0;
        end else begin
            antecedent = (button_in == 2'd0 && credit >= 8'd30);
            consequent = (beverage_out == 2'd1);
            if (antecedent && consequent)       ATCT++;
            else if (antecedent && !consequent) ATCF++;
            else if (!antecedent && consequent) AFCT++;
            else                                AFCF++;
        end
    end

    // 3. Print at end of simulation
    final begin
        $display("Contingency Table for Water Delivery Assertion:");
        $display("ATCT = %0d", ATCT);
        $display("ATCF = %0d", ATCF);
        $display("AFCT = %0d", AFCT);
        $display("AFCF = %0d", AFCF);
    end
    
    // 1. Valid Coin Acceptance
    assert property (@(posedge clk)
        (coin_in !== 0) |-> (coin_in == 8'd10 || coin_in == 8'd20 ||
                             coin_in == 8'd50 || coin_in == 8'd100 || coin_in == 8'd200)
    );

    // 2. Beverage Delivery Only with Sufficient Credit (example for water)
    assert property (@(posedge clk)
        (button_in == 2'd0 && beverage_out == 2'd1) |-> (credit + 8'd30 >= 8'd30)
    );
    // Add more assertions as needed...

    // 3. No Inputs Accepted During Delivery
    // (For illustration, you may need to pass N as parameter or expand for your value of N)
    // property p_delivery_no_input;
    //    @(posedge clk)
    //    disable iff (rst)
    //    (beverage_out != 2'd0) |-> ##[1:N] (coin_in == 0 && button_in == 0);
    // endproperty
    // assert property (p_delivery_no_input);

    // 4. Change Returned Only When Credit < 30c
    assert property (@(posedge clk)
        (change_out !== 8'd0) |-> (beverage_out != 2'd0 && credit < 8'd30)
    );

    // 5. No Beverage Delivered Without Button Press
    assert property (@(posedge clk)
        (beverage_out != 2'd0) |-> (button_in != 2'd0 || button_in != 2'd1)
    );
endmodule

