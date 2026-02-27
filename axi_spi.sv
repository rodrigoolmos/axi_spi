module axi_spi #(
    parameter integer FIFO_DEPTH = 32,
    parameter integer C_DATA_WIDTH = 32
)(
    input  logic                     clk,
    input  logic                     nrst,

    // AXI4-Lite SLAVE
    input  logic [31:0]              awaddr,
    input  logic [3:0]               awprot,
    input  logic                     awvalid,
    output logic                     awready,

    input  logic [C_DATA_WIDTH-1:0]  wdata,
    input  logic [C_DATA_WIDTH/8-1:0] wstrb,
    input  logic                     wvalid,
    output logic                     wready,

    output logic [1:0]               bresp,
    output logic                     bvalid,
    input  logic                     bready,

    input  logic [31:0]  araddr,
    input  logic [3:0]               arprot,
    input  logic                     arvalid,
    output logic                     arready,

    output logic [C_DATA_WIDTH-1:0]  rdata,
    output logic [1:0]               rresp,
    output logic                     rvalid,
    input  logic                     rready,

    // SPI physical interface
    output logic        spi_clk,
    output logic        spi_mosi,
    input  logic        spi_miso,
    output logic        spi_cs_n

);

    logic [C_DATA_WIDTH-1:0] fifo_wdata;
    logic [C_DATA_WIDTH-1:0] fifo_rdata;
    logic new_byte;
    logic spi_ena;
    logic system_idle;
    logic msb_first;
    logic delay_byte;
    logic [7:0] n_delay_byte;
    logic cpol;
    logic cpha;
    logic [23:0] clk_div;

    axi_s_to_fifos_spi #(
        .FIFO_DEPTH(FIFO_DEPTH),
        .C_DATA_WIDTH(C_DATA_WIDTH)
    ) axi_s_to_fifos_spi_i (
        .clk(clk),
        .nrst(nrst),

        .awaddr(awaddr),
        .awprot(awprot),
        .awvalid(awvalid),
        .awready(awready),

        .wdata(wdata),
        .wstrb(wstrb),
        .wvalid(wvalid),
        .wready(wready),

        .bresp(bresp),
        .bvalid(bvalid),
        .bready(bready),

        .araddr(araddr),
        .arprot(arprot),
        .arvalid(arvalid),
        .arready(arready),

        .rdata(rdata),
        .rresp(rresp),
        .rvalid(rvalid),
        .rready(rready),

        .fifo_wdata(fifo_wdata),
        .fifo_rdata(fifo_rdata),
        .new_byte(new_byte),

        .spi_busy(!system_idle),
        .spi_ena(spi_ena),

        .msb_first(msb_first),
        .delay_byte(delay_byte),
        .n_delay_byte(n_delay_byte),
        .cpol(cpol),
        .cpha(cpha),
        .clk_div(clk_div)
    );


    spi_physical spi_physical_i(
        .clk(clk),
        .nrst(nrst),

        .ena(spi_ena),
        .msb_first(msb_first),
        .delay_byte(delay_byte),
        .n_delay_byte(n_delay_byte),
        .cpol(cpol),
        .cpha(cpha),
        .clk_div(clk_div),
        .new_byte(new_byte),
        .system_idle(system_idle),
        .data_in(fifo_rdata),
        .data_out(fifo_wdata),

        .spi_clk(spi_clk),
        .spi_mosi(spi_mosi),
        .spi_miso(spi_miso),
        .spi_cs_n(spi_cs_n)
    );

endmodule