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

  
    // //Instantiate from counter module
    // counter c1(.ctrl(sig.ctrl), 
    //             .INIT(sig.INIT), 
    //             .loadValue(sig.loadValue), 
    //             .clk(sig.clk), 
    //             .rst_l(sig.rst_l), 
    //             .LOSER(sig.LOSER), 
    //             .WINNER(sig.WINNER), 
    //             .WHO(sig.WHO), 
    //             .GAMEOVER(sig.GAMEOVER));
    

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
                sig.cb.ctrl <= ctrl_c;
                if(loadValue_c == 2) sig.cb.loadValue <= {COUNTER_SIZE{1'b1}};
                else sig.cb.loadValue <= loadValue_c;
                sig.cb.INIT <= 0;
                #1
                sig.cb.rst_l <= 0;
                sig.cb.INIT <= 1;
                #2
                sig.cb.INIT <= 0;
                #481
                sig.cb.rst_l <= 1;
            end
        end
    end
    

endprogram


module top (output bit clk);
    initial clk = 1;
    initial forever #1 clk = ~clk;
    Counter_Interface iface(clk);
    tb_counter t0(iface.tb);
    counter G0(iface.dut);
    /********************************************************************************
        DUMP VARIABLES
    ********************************************************************************/
    initial begin
        $dumpfile("wave.vcd");
        $dumpvars;
        #6000 $finish;
    end

endmodule