/**********************************************************************************
	  Module name: tb_counter                                                   
      Description: testbench
      Date: April 2022                                                      
      Auther: Sarah Mohamed Ahmed  
**********************************************************************************/
program tb_counter(Counter_Interface.tb sig);
    /********************************************************************************
        PARAMETERS
    ********************************************************************************/
    parameter cycle = 2;
    parameter COUNTER_SIZE = 4;
    /********************************************************************************
        INITIAL BLOCK
    ********************************************************************************/
    initial begin
        sig.cb.loadValue <= 4'b0000;
        sig.cb.ctrl <= 2'b00;
        sig.cb.rst_l <= 1;
        sig.cb.INIT <= 0;
        for (int ctrl_c = 0; ctrl_c <= 3; ctrl_c = ctrl_c + 1) begin 
            for (int loadValue_c = 0; loadValue_c < 3; loadValue_c = loadValue_c + 1) begin   
                // sig.rst_l <= 1;
                assertion_1: assert (sig.cb.WINNER == 0)
                    $display("WINNER = %d asserted correctly", sig.cb.WINNER);
                else 
                    $fatal("WINNER = %d not asserted correctly", sig.cb.WINNER);
                sig.cb.ctrl <= ctrl_c;
                if(loadValue_c == 2) sig.cb.loadValue <= {COUNTER_SIZE{1'b1}};
                else sig.cb.loadValue <= loadValue_c;
                sig.cb.INIT <= 0;
                #1
                sig.cb.rst_l <= 0;
                sig.cb.INIT <= 1;
                #3
                sig.cb.INIT <= 0;
                #481
                sig.cb.rst_l <= 1;
            end
        end
    end
    /****************************
        Assign BLOCK
    ****************************/
    assign WHO = sig.cb.WHO;
    assign LOSER = sig.cb.LOSER;
    assign WINNER = sig.cb.WINNER;
    assign GAMEOVER = sig.cb.GAMEOVER;  
    /****************************
        Properties
    ****************************/
    property signals_cleared;
      @(sig.cb) disable iff(!($fell(sig.rst_l) )) (WHO ==0 || LOSER == 0 || GAMEOVER == 0 || WINNER ==0);
    endproperty

    property winner;
      @(sig.cb)
      if($fell(sig.rst_l)) ##[100:200] GAMEOVER ==1;
    endproperty

    /****************************
        Asserions
    ****************************/
    assert_winner: assert property(winner)$display("[%0t] ----- Assertion GameOver passed", $time);
    assert_signals_cleared: assert property (signals_cleared) $display("[%0t] ----- Assertion Reseting_signals passed", $time);
endprogram

      

module top (output bit clk);
    initial clk = 1;
    initial forever #1 clk = ~clk;
    Counter_Interface iface(clk);
    tb_counter t0(iface.tb);
    counter G0(iface.dut);
    /******************************
        DUMP VARIABLES
    ******************************/
    initial begin
        $dumpfile("wave.vcd");
        $dumpvars;
        #6000 $finish;
    end

endmodule