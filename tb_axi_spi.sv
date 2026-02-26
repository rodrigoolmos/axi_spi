`timescale 1us/1ns
`include "axi_s_to_fifos/axi_lite_template/agent_axi_lite.sv"
`include "agent_spi_slave.sv"

module tb_axi_spi;

    const integer t_clk    = 10;    // Clock period 100MHz

    localparam ADDR_WIDTH = 32;
    localparam DATA_WIDTH = 32;

    localparam ADDR_STATUS      = 0;
    localparam ADDR_WRITE       = 1;
    localparam ADDR_READ        = 2;
    localparam ADDR_N_BYTE_W_R  = 3;
    localparam ADDR_DELAYS      = 4;
    localparam ADDR_CLK_DIV     = 5;
    localparam ADDR_CFG         = 6;

    logic        active_frame;
    logic        msb_first;
    logic        delay_byte;
    logic [7:0]  n_delay_byte;
    logic        cpol;
    logic        cpha;
    logic [23:0] clk_div;

    spi_if spi_if();

    spi_slave spi_slave_inst;

    spi_cfg_t spi_cfg;

    logic [7:0] read_data[$];
    logic [7:0] write_data[$];

    assign spi_if.clk = axi_if.clk;
    assign spi_if.nrst = axi_if.nrst;
    assign spi_if.spi_cfg.msb_first = msb_first;
    assign spi_if.spi_cfg.delay_byte = delay_byte;
    assign spi_if.spi_cfg.n_delay_byte = n_delay_byte;
    assign spi_if.spi_cfg.cpha = cpha;
    assign spi_if.spi_cfg.cpol = cpol;
    assign spi_if.spi_cfg.clk_div = clk_div;
    assign spi_if.active_frame = active_frame;

    axi_if #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) axi_if();

    axi_lite_master #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) master;

    axi_spi #(
        .C_DATA_WIDTH(DATA_WIDTH),
        .FIFO_DEPTH(8)
    ) dut (
        .clk    (axi_if.clk),
        .nrst    (axi_if.nrst),

        // AXI4-Lite SLAVE
        .awaddr (axi_if.awaddr),
        .awprot (axi_if.awprot),
        .awvalid(axi_if.awvalid),
        .awready(axi_if.awready),

        .wdata  (axi_if.wdata),
        .wstrb  (axi_if.wstrb),
        .wvalid (axi_if.wvalid),
        .wready (axi_if.wready),

        .bresp  (axi_if.bresp),
        .bvalid (axi_if.bvalid),
        .bready (axi_if.bready),

        .araddr (axi_if.araddr),
        .arprot (axi_if.arprot),
        .arvalid(axi_if.arvalid),
        .arready(axi_if.arready),

        .rdata  (axi_if.rdata),
        .rresp  (axi_if.rresp),
        .rvalid (axi_if.rvalid),
        .rready (axi_if.rready),

        // SPI physical interface
        .spi_clk (spi_if.sclk),
        .spi_mosi(spi_if.mosi),
        .spi_miso(spi_if.miso),
        .spi_cs_n(spi_if.cs_n)
    );

    task automatic configure_spi(spi_cfg_t cfg);
            msb_first = cfg.msb_first;
            delay_byte = cfg.delay_byte;
            n_delay_byte = cfg.n_delay_byte;
            cpol = cfg.cpol;
            cpha = cfg.cpha;
            clk_div = cfg.clk_div;
            spi_slave_inst.configure_mode(cfg);
    endtask

    task generate_spi_trans(spi_cfg_t cfg, int ndata_write, int ndata_read);
        logic [31:0] read_data_tmp;
        logic [15:0] ndata_write_tmp;
        logic [15:0] ndata_read_tmp;
        logic [31:0] write_data_tmp;
        // Configure SPI slave settings
        configure_spi(cfg);
        // Configure SPI master settings
        master.write({24'h0, cfg.clk_div}, ADDR_CLK_DIV*4, 4'b1111);
        master.write({23'h0, cfg.delay_byte, cfg.n_delay_byte}, ADDR_DELAYS*4, 4'b1111);
        master.write({24'h0, cfg.cpha, cfg.cpol, cfg.msb_first}, ADDR_CFG*4, 4'b1111);

        // Write data to be transmitted
        for (int i = 0; i < ndata_write; i++) begin
            write_data.push_back(i);
            master.write({24'h0, write_data[i]}, ADDR_WRITE*4, 4'b1111);
        end

        // Start SPI
        ndata_read_tmp = ndata_read;
        ndata_write_tmp = ndata_write;
        write_data_tmp = {ndata_write_tmp, ndata_read_tmp};
        master.write(write_data_tmp, ADDR_N_BYTE_W_R*4, 4'b1111);

        // Wait write transaction to complete
        @(posedge axi_if.clk iff dut.axi_s_to_fifos_spi_i.n_bytes_to_write == 0);

        // Slave writes data to be read by master
        for (int i = 0; i < ndata_read; i++) begin
            spi_slave_inst.write();
        end

        // Wait for SPI transaction to complete
        read_data_tmp = 0;
        while (read_data_tmp & 5'b10000 == 0) begin
            master.read(read_data_tmp, ADDR_STATUS*4);
            @(posedge axi_if.clk);
        end

        // Read received data
        for (int i = 0; i < ndata_read; i++) begin
            master.read(read_data_tmp, ADDR_READ*4);
            read_data.push_back(read_data_tmp[7:0]);
        end

    endtask

    // Clock generation 
    initial begin
        axi_if.clk = 0;
        forever #(t_clk/2) axi_if.clk = ~axi_if.clk;
    end

    // Reset generation and initialization
    initial begin
        axi_if.nrst = 0;
        master = new(axi_if);
        master.reset_if();
        spi_slave_inst = new(spi_if);
        spi_slave_inst.reset_if();
        #100 @(posedge axi_if.clk);
        axi_if.nrst = 1;
        @(posedge axi_if.clk);
    end

    initial begin
        spi_cfg_t cfg;
        @(posedge axi_if.nrst);
        #100 @(posedge axi_if.clk);

        // Test case 1: Simple write and read
        cfg = '{msb_first: 1, delay_byte: 1, n_delay_byte: 2, cpol: 0, cpha: 0, clk_div: 4};
        generate_spi_trans(cfg, 4, 4);


        #10000 @(posedge axi_if.clk);

        $stop;

    end

endmodule