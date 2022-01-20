// SPDX-FileCopyrightText: 2020 Efabless Corporation
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// SPDX-License-Identifier: Apache-2.0

`default_nettype none
/*
 *-------------------------------------------------------------
 *
 * user_proj_example
 *
 * This is an example of a (trivially simple) user project,
 * showing how the user project can connect to the logic
 * analyzer, the wishbone bus, and the I/O pads.
 *
 * This project generates an integer count, which is output
 * on the user area GPIO pads (digital output only).  The
 * wishbone connection allows the project to be controlled
 * (start and stop) from the management SoC program.
 *
 * See the testbenches in directory "mprj_counter" for the
 * example programs that drive this user project.  The three
 * testbenches are "io_ports", "la_test1", and "la_test2".
 *
 *-------------------------------------------------------------
 */

module user_proj_example #(
    parameter BITS = 32
)(
`ifdef USE_POWER_PINS
    inout vccd1,	// User area 1 1.8V supply
    inout vssd1,	// User area 1 digital ground
`endif

    // Wishbone Slave ports (WB MI A)
    input wb_clk_i,
    input wb_rst_i,
    input wbs_stb_i,
    input wbs_cyc_i,
    input wbs_we_i,
    input [3:0] wbs_sel_i,
    input [31:0] wbs_dat_i,
    input [31:0] wbs_adr_i,
    output wbs_ack_o,
    output [31:0] wbs_dat_o,

    // Logic Analyzer Signals
    input  [127:0] la_data_in,
    output [127:0] la_data_out,
    input  [127:0] la_oenb,

    // IOs
    input  [`MPRJ_IO_PADS-1:0] io_in,
    output [`MPRJ_IO_PADS-1:0] io_out,
    output [`MPRJ_IO_PADS-1:0] io_oeb,

    // IRQ
    output [2:0] irq
);
    /*
    wire clk;
    wire rst;
    */
    wire [`MPRJ_IO_PADS-1:0] io_in;
    wire [`MPRJ_IO_PADS-1:0] io_out;
    wire [`MPRJ_IO_PADS-1:0] io_oeb;

    wire [15:0] sum1;
    wire cout1;
    wire [15:0] a1, b1;
    
    assign {b1,a1}=[`MPRJ_IO_PADS-7:0] io_in;
    assign io_out={21'd0,cout1,sum1};
    assign io_oeb={21'd0,17'd1};
    /*
    wire [31:0] rdata; 
    wire [31:0] wdata;
    wire [BITS-1:0] count;

    wire valid;
    wire [3:0] wstrb;
    wire [31:0] la_write;

    // WB MI A
    assign valid = wbs_cyc_i && wbs_stb_i; 
    assign wstrb = wbs_sel_i & {4{wbs_we_i}};
    assign wbs_dat_o = rdata;
    assign wdata = wbs_dat_i;

    // IO
    assign io_out = count;
    assign io_oeb = {(`MPRJ_IO_PADS-1){rst}};

    // IRQ
    assign irq = 3'b000;	// Unused

    // LA
    assign la_data_out = {{(127-BITS){1'b0}}, count};
    // Assuming LA probes [63:32] are for controlling the count register  
    assign la_write = ~la_oenb[63:32] & ~{BITS{valid}};
    // Assuming LA probes [65:64] are for controlling the count clk & reset  
    assign clk = (~la_oenb[64]) ? la_data_in[64]: wb_clk_i;
    assign rst = (~la_oenb[65]) ? la_data_in[65]: wb_rst_i;
     */
     KSA16 ins1(sum, cout, a, b);
endmodule

module BigCircle(output G, P, input Gi, Pi, GiPrev, PiPrev);
  
  wire e;
  and #(1) (e, Pi, GiPrev);
  or #(1) (G, e, Gi);
  and #(1) (P, Pi, PiPrev);
  
endmodule

module SmallCircle(output Ci, input Gi);
  
  buf #(1) (Ci, Gi);
  
endmodule

module Square(output G, P, input Ai, Bi);
  
  and #(1) (G, Ai, Bi);
  xor #(2) (P, Ai, Bi);
  
endmodule

module Triangle(output Si, input Pi, CiPrev);
  
  xor #(2) (Si, Pi, CiPrev);
  
endmodule


module KSA16(output [15:0] sum, output cout, input [15:0] a, b);
  
  wire cin = 1'b0;
  wire [15:0] c;
  wire [15:0] g, p;
    
    /*
  Square sq[15:0](g, p, a, b);

  // first line of circles
  wire [15:1] g2, p2;
  SmallCircle sc0_0(c[0], g[0]);
  BigCircle bc0[15:1](g2[15:1], p2[15:1], g[15:1], p[15:1], g[14:0], p[14:0]);
  
  // second line of circle
  wire [15:3] g3, p3;
  SmallCircle sc1[2:1](c[2:1], g2[2:1]);
  BigCircle bc1[15:3](g3[15:3], p3[15:3], g2[15:3], p2[15:3], g2[13:1], p2[13:1]);
  
  // third line of circle
  wire [15:7] g4, p4;
  SmallCircle sc2[6:3](c[6:3], g3[6:3]);
  BigCircle bc2[15:7](g4[15:7], p4[15:7], g3[15:7], p3[15:7], g3[11:3], p3[11:3]);

  // fourth line of circle
  wire [15:15] g5, p5;
  SmallCircle sc3[14:7](c[14:7], g4[14:7]);
  BigCircle bc3_15(g5[15], p5[15], g4[15], p4[15], g4[7], p4[7]);  
  
  // fifth line of circle
  SmallCircle sc4_15(c[15], g5[15]);
  
  // last line - triangles
  Triangle tr0(sum[0], p[0], cin);
  Triangle tr[15:1](sum[15:1], p[15:1], c[14:0]);

  // generate cout
  buf #(1) (cout, c[15]);
*/
    
    genvar i,j;
    generate for(i=0; i<16; i=i+1) begin : test1
  //Square sq[15:0](g, p, a, b);
        Square sq(g[i], p[i], a[i], b[i]);
    end
    endgenerate

  // first line of circles
  wire [15:1] g2, p2;
  SmallCircle sc0_0(c[0], g[0]);
  //BigCircle bc0[15:1](g2[15:1], p2[15:1], g[15:1], p[15:1], g[14:0], p[14:0]);
    generate for(j=1; j<16; j=j+1) begin : test2
  //BigCircle bc0[15:1](g2[15:1], p2[15:1], g[15:1], p[15:1], g[14:0], p[14:0]);
        BigCircle bc0(g2[j], p2[j], g[j], p[j], g[j-1], p[j-1]);
    end
    endgenerate

  // second line of circle
  wire [15:3] g3, p3;
//  SmallCircle sc1[2:1](c[2:1], g2[2:1]);
 // BigCircle bc1[15:3](g3[15:3], p3[15:3], g2[15:3], p2[15:3], g2[13:1], p2[13:1]);

    genvar k;
    generate for(k=1; k<3; k=k+1) begin : test2
  //SmallCircle sc1[2:1](c[2:1], g2[2:1]);
        SmallCircle sc1(c[k], g2[k]);
    end
    endgenerate

    genvar i1;
    generate for(i1=3;i1<16;i1=i1+1) begin: test3
  //BigCircle bc1[15:3](g3[15:3], p3[15:3], g2[15:3], p2[15:3], g2[13:1], p2[13:1]);
        BigCircle bc1(g3[i1], p3[i1], g2[i1], p2[i1], g2[i1-2], p2[i1-2]);
    end
    endgenerate
  // third line of circle
  wire [15:7] g4, p4;
  //SmallCircle sc2[6:3](c[6:3], g3[6:3]);
  //BigCircle bc2[15:7](g4[15:7], p4[15:7], g3[15:7], p3[15:7], g3[11:3], p3[11:3]);
    genvar j1;
    generate for(j1=3; j1<7; j1=j1+1) begin:test4
  //SmallCircle sc2[6:3](c[6:3], g3[6:3]);
        SmallCircle sc2(c[j1], g3[j1]);
    end
    endgenerate
    genvar k1;
    generate for(k1=7; k1<16; k1=k1+1) begin:test5
  //BigCircle bc2[15:7](g4[15:7], p4[15:7], g3[15:7], p3[15:7], g3[11:3], p3[11:3]);
        BigCircle bc2(g4[k1], p4[k1], g3[k1], p3[k1], g3[k1-4], p3[k1-4]);
    end
    endgenerate

  // fourth line of circle
  wire [15:15] g5, p5;
  //SmallCircle sc3[14:7](c[14:7], g4[14:7]);
    genvar m1,m2;
    generate for(m1=7; m1<15; m1=m1+1) begin:test6

  //SmallCircle sc3[14:7](c[14:7], g4[14:7]);
        SmallCircle sc3(c[m1], g4[m1]);
    end
        endgenerate

  BigCircle bc3_15(g5[15], p5[15], g4[15], p4[15], g4[7], p4[7]);  

  // fifth line of circle
  SmallCircle sc4_15(c[15], g5[15]);

  // last line - triangles
  Triangle tr0(sum[0], p[0], cin);
  //Triangle tr[15:1](sum[15:1], p[15:1], c[14:0]);
    generate for(m2=1; m2<16; m2=m2+1) begin:test7
  //Triangle tr[15:1](sum[15:1], p[15:1], c[14:0]);
        Triangle tr(sum[m2], p[m2], c[m2-1]);
    end
    endgenerate

  // generate cout
  buf #(1) (cout, c[15]);
endmodule
`default_nettype wire
