`timescale 1us/1ns
`include "axi_s_to_fifos/axi_lite_template/agent_axi_lite.sv"
`include "agent_spi_slave.sv"

module tb_axi_spi;

    const integer t_clk = 10;    // Clock period 100MHz

    localparam ADDR_WIDTH = 32;
    localparam DATA_WIDTH = 32;
    localparam FIFO_DEPTH = 8;

    localparam ADDR_STATUS      = 0;
    localparam ADDR_WRITE       = 1;
    localparam ADDR_READ        = 2;
    localparam ADDR_N_BYTE_W_R  = 3;
    localparam ADDR_DELAYS      = 4;
    localparam ADDR_CLK_DIV     = 5;
    localparam ADDR_CFG         = 6;

    localparam int N_RANDOM_MAIN = 120;
    localparam int N_RANDOM_CORNER = 40;
    // Large limits to cover worst-case random settings (clk_div up to 105 and
    // n_delay_byte up to 255) without false timeouts.
    localparam int MAX_IDLE_POLLS = 200000;
    localparam int MAX_WRITE_PHASE_CYCLES = 1000000;

    logic        msb_first;
    logic        delay_byte;
    logic [7:0]  n_delay_byte;
    logic        cpol;
    logic        cpha;
    logic [23:0] clk_div;

    spi_if spi_if();

    spi_slave spi_slave_inst;

    logic [7:0] write_data[$];

    int mode_cov[2][2][2];
    int delay_cov[5];
    int clkdiv_cov[6];
    int n_transactions;
    int n_bytes_tx;
    int n_bytes_rx;

    assign spi_if.clk = axi_if.clk;
    assign spi_if.nrst = axi_if.nrst;
    // Drive assertion/config monitor with the configuration actually applied in DUT
    assign spi_if.spi_cfg.msb_first = dut.msb_first;
    assign spi_if.spi_cfg.delay_byte = dut.delay_byte;
    assign spi_if.spi_cfg.n_delay_byte = dut.n_delay_byte;
    assign spi_if.spi_cfg.cpha = dut.cpha;
    assign spi_if.spi_cfg.cpol = dut.cpol;
    assign spi_if.spi_cfg.clk_div = dut.clk_div;
    assign spi_if.active_frame = dut.spi_ena;

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
        .FIFO_DEPTH(FIFO_DEPTH)
    ) dut (
        .clk    (axi_if.clk),
        .nrst   (axi_if.nrst),

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

    function automatic int imin(input int a, input int b);
        return (a < b) ? a : b;
    endfunction

    function automatic int delay_bin(input int unsigned dly);
        if (dly == 0) return 0;
        if (dly == 1) return 1;
        if (dly <= 3) return 2;
        if (dly <= 7) return 3;
        return 4;
    endfunction

    function automatic int clkdiv_bin(input int unsigned divv);
        if (divv <= 6) return 0;
        if (divv <= 10) return 1;
        if (divv <= 20) return 2;
        if (divv <= 50) return 3;
        if (divv <= 100) return 4;
        return 5;
    endfunction

    function automatic int pick_len(input int max_len);
        int sel;
        if (max_len <= 0) return 0;
        sel = $urandom_range(0, 9);
        case (sel)
            0: return 0;
            1: return 1;
            2: return max_len;
            default: return $urandom_range(0, max_len);
        endcase
    endfunction

    task automatic configure_spi(spi_cfg_t cfg);
        msb_first = cfg.msb_first;
        delay_byte = cfg.delay_byte;
        n_delay_byte = cfg.n_delay_byte;
        cpol = cfg.cpol;
        cpha = cfg.cpha;
        clk_div = cfg.clk_div;
        spi_slave_inst.configure_mode(cfg);
    endtask

    task automatic sample_coverage(spi_cfg_t cfg, int ndata_write, int ndata_read);
        if ((ndata_write + ndata_read) == 0) begin
            return;
        end
        mode_cov[cfg.msb_first][cfg.cpol][cfg.cpha]++;
        delay_cov[delay_bin(cfg.n_delay_byte)]++;
        clkdiv_cov[clkdiv_bin(cfg.clk_div)]++;
        n_transactions++;
        n_bytes_tx += ndata_write;
        n_bytes_rx += ndata_read;
    endtask

    task automatic read_status(output logic [31:0] status);
        master.read(status, ADDR_STATUS*4);
    endtask

    task automatic wait_spi_idle(input int max_polls = MAX_IDLE_POLLS);
        logic [31:0] status;
        for (int i = 0; i < max_polls; i++) begin
            read_status(status);
            if (!status[4]) begin
                return;
            end
        end
        $fatal(1, "Timeout waiting SPI idle (status[4] stayed high)");
    endtask

    task automatic wait_write_phase_done(input int max_cycles = MAX_WRITE_PHASE_CYCLES);
        for (int i = 0; i < max_cycles; i++) begin
            @(posedge axi_if.clk);
            if (dut.axi_s_to_fifos_spi_i.n_bytes_to_write == 0) begin
                return;
            end
        end
        $fatal(1, "Timeout waiting n_bytes_to_write == 0");
    endtask

    task automatic check_model_consistency(input int ndata_remaining, input string where_tag);
        assert (write_data.size() == ndata_remaining)
            else $fatal(1, "[%s] queue mismatch: write_data.size=%0d expected=%0d",
                where_tag, write_data.size(), ndata_remaining);
        assert (spi_slave_inst.buffer_read.size() == ndata_remaining)
            else $fatal(1, "[%s] slave buffer mismatch: buffer_read.size=%0d expected=%0d",
                where_tag, spi_slave_inst.buffer_read.size(), ndata_remaining);
    endtask

    task automatic generate_spi_trans(spi_cfg_t cfg, int ndata_write, int ndata_read);
        logic [31:0] read_data_tmp;
        logic [31:0] expe_data_tmp;
        logic [15:0] ndata_write_tmp;
        logic [15:0] ndata_read_tmp;
        logic [31:0] write_data_tmp;
        logic [7:0] tx_byte;

        // Driver contract: configure and trigger only when peripheral is idle
        wait_spi_idle();

        // Configure SPI slave settings
        configure_spi(cfg);

        // Configure SPI master settings
        master.write({24'h0, cfg.clk_div}, ADDR_CLK_DIV*4, 4'b1111);
        master.write({23'h0, cfg.delay_byte, cfg.n_delay_byte}, ADDR_DELAYS*4, 4'b1111);
        master.write({24'h0, cfg.cpha, cfg.cpol, cfg.msb_first}, ADDR_CFG*4, 4'b1111);

        // Write data to be transmitted
        for (int i = 0; i < ndata_write; i++) begin
            tx_byte = $urandom_range(0, 255);
            write_data.push_back(tx_byte);
            master.write({24'h0, tx_byte}, ADDR_WRITE*4, 4'b1111);
        end

        // Start SPI
        ndata_read_tmp = ndata_read;
        ndata_write_tmp = ndata_write;
        write_data_tmp = {ndata_write_tmp, ndata_read_tmp};
        master.write(write_data_tmp, ADDR_N_BYTE_W_R*4, 4'b1111);

        fork
            spi_slave_inst.read(ndata_write_tmp);
            begin
                wait_write_phase_done();
                spi_slave_inst.write(ndata_read_tmp);
            end
        join

        // Wait for SPI transaction to complete (black-box view via status)
        wait_spi_idle();

        // Read received data and compare against reference model queue
        for (int i = 0; i < ndata_read; i++) begin
            master.read(read_data_tmp, ADDR_READ*4);
            expe_data_tmp = write_data.pop_front();
            assert (read_data_tmp[7:0] == expe_data_tmp[7:0])
                else $fatal(1, "Data mismatch at byte %0d: expected 0b%08b, got 0b%08b",
                     i, expe_data_tmp[7:0], read_data_tmp[7:0]);
        end
    endtask

    task automatic run_transaction(
        input spi_cfg_t cfg,
        input int ndata_write,
        input int ndata_read,
        inout int ndata_remaining,
        input string where_tag
    );
        int ndata_after;

        assert (ndata_write >= 0 && ndata_read >= 0)
            else $fatal(1, "[%s] negative lengths are invalid", where_tag);

        assert (ndata_write <= (FIFO_DEPTH - ndata_remaining))
            else $fatal(1, "[%s] write overflow request: nwrite=%0d free=%0d",
                where_tag, ndata_write, FIFO_DEPTH - ndata_remaining);

        assert (ndata_read <= (ndata_remaining + ndata_write))
            else $fatal(1, "[%s] read underflow request: nread=%0d available=%0d",
                where_tag, ndata_read, ndata_remaining + ndata_write);

        ndata_after = ndata_remaining + ndata_write - ndata_read;
        sample_coverage(cfg, ndata_write, ndata_read);
        generate_spi_trans(cfg, ndata_write, ndata_read);
        ndata_remaining = ndata_after;
        check_model_consistency(ndata_remaining, where_tag);
    endtask

    task automatic run_directed_suite(inout int ndata_remaining);
        spi_cfg_t cfg;
        int nwrite;
        int nread;

        $display("Running directed suite");

        // Sweep all SPI mode combinations with and without delay
        for (int m = 0; m < 2; m++) begin
            for (int p = 0; p < 2; p++) begin
                for (int h = 0; h < 2; h++) begin
                    cfg = '{msb_first: m, delay_byte: 0, n_delay_byte: 0, cpol: p, cpha: h,
                            clk_div: 8 + (m*4) + (p*2) + h};
                    nwrite = ((FIFO_DEPTH - ndata_remaining) > 0) ? 1 : 0;
                    nread = ((ndata_remaining + nwrite) > 0) ? 1 : 0;
                    if (nwrite || nread) begin
                        run_transaction(cfg, nwrite, nread, ndata_remaining,
                            $sformatf("DIR_MODE_NDLY_m%0d_p%0d_h%0d", m, p, h));
                    end

                    cfg = '{msb_first: m, delay_byte: 1, n_delay_byte: 1 + (m*4) + (p*2) + h,
                            cpol: p, cpha: h, clk_div: 16 + (m*4) + (p*2) + h};
                    nwrite = ((FIFO_DEPTH - ndata_remaining) > 0) ? 1 : 0;
                    nread = ((ndata_remaining + nwrite) > 0) ? 1 : 0;
                    if (nwrite || nread) begin
                        run_transaction(cfg, nwrite, nread, ndata_remaining,
                            $sformatf("DIR_MODE_DLY_m%0d_p%0d_h%0d", m, p, h));
                    end
                end
            end
        end

        // Fill then drain to hit FIFO boundary behavior
        cfg = '{msb_first: 1, delay_byte: 1, n_delay_byte: 4, cpol: 1, cpha: 1, clk_div: 32};
        nwrite = FIFO_DEPTH - ndata_remaining;
        if (nwrite > 0) begin
            run_transaction(cfg, nwrite, 0, ndata_remaining, "DIR_FILL_FIFO");
        end
        if (ndata_remaining > 0) begin
            run_transaction(cfg, 0, ndata_remaining, ndata_remaining, "DIR_DRAIN_FIFO");
        end

        // Extra write-only, read-only and mixed cases
        cfg = '{msb_first: 0, delay_byte: 1, n_delay_byte: 2, cpol: 0, cpha: 1, clk_div: 12};
        nwrite = imin(3, FIFO_DEPTH - ndata_remaining);
        if (nwrite > 0) begin
            run_transaction(cfg, nwrite, 0, ndata_remaining, "DIR_WRITE_ONLY");
        end

        nread = imin(2, ndata_remaining);
        if (nread > 0) begin
            run_transaction(cfg, 0, nread, ndata_remaining, "DIR_READ_ONLY");
        end

        nwrite = imin(2, FIFO_DEPTH - ndata_remaining);
        nread = imin(2, ndata_remaining + nwrite);
        if (nwrite || nread) begin
            run_transaction(cfg, nwrite, nread, ndata_remaining, "DIR_MIXED");
        end
    endtask

    task automatic run_random_suite(input int n_tests, input bit wide_delay_range, inout int ndata_remaining);
        spi_cfg_t cfg;
        int nwrite;
        int nread;
        int free_slots;
        int available_to_read;

        for (int i = 0; i < n_tests; i++) begin
            cfg = '{
                msb_first: $urandom_range(0, 1),
                delay_byte: $urandom_range(0, 1),
                n_delay_byte: wide_delay_range ? $urandom_range(0, 255) : $urandom_range(0, 7),
                cpol: $urandom_range(0, 1),
                cpha: $urandom_range(0, 1),
                clk_div: $urandom_range(5, 105)
            };

            free_slots = FIFO_DEPTH - ndata_remaining;
            nwrite = pick_len(free_slots);
            available_to_read = ndata_remaining + nwrite;
            nread = pick_len(available_to_read);

            // Avoid no-op transactions so every iteration stresses datapath
            if ((nwrite == 0) && (nread == 0)) begin
                if (free_slots > 0) begin
                    nwrite = 1;
                end else if (available_to_read > 0) begin
                    nread = 1;
                end
            end

            run_transaction(cfg, nwrite, nread, ndata_remaining,
                $sformatf("RAND_%0d", i));

            if (((i + 1) % 25) == 0) begin
                $display("Random progress %0d/%0d outstanding=%0d",
                    i + 1, n_tests, ndata_remaining);
            end
        end
    endtask

    task automatic report_coverage();
        int missing_modes;

        missing_modes = 0;
        for (int m = 0; m < 2; m++) begin
            for (int p = 0; p < 2; p++) begin
                for (int h = 0; h < 2; h++) begin
                    $display("Coverage mode m%0d p%0d h%0d = %0d",
                        m, p, h, mode_cov[m][p][h]);
                    if (mode_cov[m][p][h] == 0) begin
                        missing_modes++;
                    end
                end
            end
        end

        $display("Coverage delay bins [0,1,2-3,4-7,8+] = [%0d, %0d, %0d, %0d, %0d]",
            delay_cov[0], delay_cov[1], delay_cov[2], delay_cov[3], delay_cov[4]);
        $display("Coverage clkdiv bins [5-6,7-10,11-20,21-50,51-100,101+] = [%0d, %0d, %0d, %0d, %0d, %0d]",
            clkdiv_cov[0], clkdiv_cov[1], clkdiv_cov[2], clkdiv_cov[3], clkdiv_cov[4], clkdiv_cov[5]);

        assert (missing_modes == 0)
            else $fatal(1, "Missing SPI mode coverage bins: %0d", missing_modes);
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
        spi_cfg_t cfg_init;
        int ndata_remaining;

        cfg_init = '{msb_first: 0, delay_byte: 0, n_delay_byte: 0, cpol: 0, cpha: 0, clk_div: 5};
        configure_spi(cfg_init);
        @(posedge axi_if.nrst);
        #100 @(posedge axi_if.clk);

        write_data.delete();
        ndata_remaining = 0;

        run_directed_suite(ndata_remaining);
        run_random_suite(N_RANDOM_MAIN, 1'b1, ndata_remaining);
        run_random_suite(N_RANDOM_CORNER, 1'b0, ndata_remaining);

        // Flush remaining expected bytes and leave model empty
        if (ndata_remaining > 0) begin
            cfg_init = '{msb_first: 1, delay_byte: 0, n_delay_byte: 0, cpol: 0, cpha: 0, clk_div: 18};
            run_transaction(cfg_init, 0, ndata_remaining, ndata_remaining, "FINAL_FLUSH");
        end

        check_model_consistency(ndata_remaining, "FINAL");
        assert (ndata_remaining == 0)
            else $fatal(1, "Outstanding bytes after test end: %0d", ndata_remaining);

        report_coverage();

        $display("TB PASSED: transactions=%0d tx_bytes=%0d rx_bytes=%0d",
            n_transactions, n_bytes_tx, n_bytes_rx);

        #1000 @(posedge axi_if.clk);
        $stop;
    end

endmodule
