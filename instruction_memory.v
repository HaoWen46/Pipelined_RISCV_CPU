module instruction_memory #(
    parameter ADDR_W   = 64,
    parameter INST_W   = 32,
    parameter MAX_INST = 256
)(
    input               i_clk,
    input               i_rst_n,
    input               i_valid,
    input  [ADDR_W-1:0] i_addr,
    output              o_valid,
    output [INST_W-1:0] o_inst
);
 
    reg [INST_W-1:0] mem [0:MAX_INST-1];

    assign o_valid = i_valid;
    assign o_inst = (i_valid) ? mem[i_addr/4] : 0;
    
/*
    reg [INST_W-1:0] o_inst_r,  o_inst_w;
    reg              o_valid_r, o_valid_w;
    
    reg [INST_W-1:0] temp1_r, temp1_w;
    reg [INST_W-1:0] temp2_r, temp2_w;
    reg              temp1_valid_r, temp1_valid_w;
    reg              temp2_valid_r, temp2_valid_w;
    
    assign o_valid = o_valid_r;
    assign o_inst  = o_inst_r;
    
    always @(*) begin
        o_valid_w = (i_valid) ? 1 : 0;
        o_inst_w  = (i_valid) ? mem[i_addr/4] : 0;
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (~i_rst_n) begin
            o_valid_r     <= 0;
            o_inst_r      <= 0;
        end else begin
            o_valid_r     <= o_valid_w;
            o_inst_r      <= o_inst_w;
        end
    end
*/
endmodule 
