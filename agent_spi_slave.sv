interface spi_if;
    
    logic clk;
    logic nrst;
    logic sclk;
    logic mosi;
    logic miso;
    logic cs_n;
    logic cpha;
    logic cpol;
    logic active_frame;

    property scl_while_cs_n_low; //clk>>sclk
        @(posedge clk) disable iff (!nrst)
            ($rose(sclk) || $fell(sclk)) && !($rose(cpol) || $fell(cpol)) |-> !cs_n;
    endproperty
    assert property (scl_while_cs_n_low) 
        else $error("SPI clock toggled while CS_N was high");

    property sclk_idle_matches_cpol_when_cs_high;
        @(posedge clk) disable iff (!nrst)
            cs_n |-> cpol == sclk;
    endproperty
    assert property (sclk_idle_matches_cpol_when_cs_high)
        else $error("SPI clock polarity mismatch while CS_N was high");

    property no_x_during_transfer;
        @(posedge clk) disable iff (!nrst)
            (!cs_n) |-> !$isunknown({sclk, mosi, miso, cpol, cpha, cs_n});
    endproperty
    assert property (no_x_during_transfer)
        else $error("X/Z detected on SPI signals while CS_N low");

    property no_cs_during_transfer;
        @(posedge clk) disable iff (!nrst)
            $rose(cs_n) |=> !active_frame;
    endproperty
    assert property (no_cs_during_transfer)
        else $error("CS_N glitch detected during SPI transfer");


    parameter int GUARD_CYC = 2;

    sequence sample_edge;
        (!cs_n) && (
            ( $rose(sclk) && ~(cpha ^ cpol) ) ||
            ( $fell(sclk) &&  (cpha ^ cpol) )
        );
    endsequence

    property no_mosi_change_after_sample;
        @(posedge clk) disable iff (!nrst)
            sample_edge |-> !$changed(mosi)[*GUARD_CYC];
    endproperty
    assert property(no_mosi_change_after_sample)
        else $error("MOSI changed within %0d cycles after sample edge", GUARD_CYC);

    property no_sample_edge_after_mosi_change;
    @(posedge clk) disable iff (!nrst)
        $past($changed(mosi), 1) |-> !(
        ( ($rose(sclk) && ~(cpha ^ cpol)) ||
            ($fell(sclk) &&  (cpha ^ cpol)) )
        );
    endproperty


    assert property(no_sample_edge_after_mosi_change)
        else $error("Sample edge detected within %0d cycles after MOSI change", GUARD_CYC);

    property mode_static_during_transfer;
        @(posedge clk) disable iff(!nrst)
            (!cs_n) |-> (!$changed(cpol) && !$changed(cpha));
    endproperty
    assert property(mode_static_during_transfer)
        else $error("SPI mode (CPOL/CPHA) changed during transfer");

endinterface

typedef struct packed {
    logic        msb_first;
    logic        delay_byte;
    logic [7:0]  n_delay_byte;
    logic        cpol;
    logic        cpha;
    logic [23:0] clk_div;
} spi_cfg_t;

class spi_slave;

    virtual spi_if spi_s_if;
    spi_cfg_t spi_cfg;

    logic [7:0] buffer_read[$];

    function new(virtual spi_if spi_s_if);
        this.spi_s_if = spi_s_if;
    endfunction

    task reset_if();
        spi_s_if.miso = 0;
    endtask

    task configure_mode(spi_cfg_t spi_cfg);
        this.spi_cfg = spi_cfg;
    endtask

    function automatic bit sample_on_posedge(bit cpol, bit cpha);
        bit leading_is_pos = (cpol == 0);
        return (cpha == 0) ? leading_is_pos : !leading_is_pos;
    endfunction

    task write_byte();
        logic [7:0] data;
        bit sample_pos;
        bit update_pos;
        int bit_idx;

        data       = buffer_read.pop_front();
        sample_pos = sample_on_posedge(spi_cfg.cpol, spi_cfg.cpha);
        update_pos = !sample_pos;

        for (int i = 0; i < 8; i++) begin
            bit_idx = spi_cfg.msb_first ? (7-i) : i;

            if (spi_cfg.cpha || (i != 0)) begin
                if (update_pos) @(posedge spi_s_if.sclk);
                else            @(negedge spi_s_if.sclk);
            end

            spi_s_if.miso = data[bit_idx];

            if (sample_pos) @(posedge spi_s_if.sclk);
            else            @(negedge spi_s_if.sclk);
        end

        $display("Sent byte: 0b%08b", data);
    endtask



    task write();
        wait(!spi_s_if.cs_n);
        fork
            forever begin
                if (buffer_read.size() > 0) write_byte();
                else wait (buffer_read.size() > 0);
            end 
            wait(spi_s_if.cs_n);
        join_any
        spi_s_if.miso = 0;

        disable fork;
    endtask

    task read_byte();
        logic [7:0] data;
        bit sample_pos;

        sample_pos = sample_on_posedge(spi_cfg.cpol, spi_cfg.cpha);

        for (int i=0; i<8; ++i) begin
            if (sample_pos) @(posedge spi_s_if.sclk); 
            else @(negedge spi_s_if.sclk); 
                
            data[spi_cfg.msb_first ? 7-i : i] = spi_s_if.mosi; 
        end
        $display("Received byte: 0b%08b", data);
        buffer_read.push_back(data);
    endtask

    task read();
        wait(!spi_s_if.cs_n);
        fork
            forever read_byte();
            wait(spi_s_if.cs_n);
        join_any

        disable fork;
    endtask


    task miss_match_ndata(int n_data);
        int cnt_edges = 0;
        wait(!spi_s_if.cs_n);
        fork
            forever begin
                @(edge spi_s_if.sclk);
                cnt_edges++;
            end
            begin
                wait(spi_s_if.cs_n);
                assert (cnt_edges == n_data*16) else 
                    $error("Expected %0d edges for %0d bytes, but got %0d", n_data*16, n_data, cnt_edges);
            end
        join_any
        disable fork;
    endtask

    task frame_assertions(int n_data);
        miss_match_ndata(n_data);
    endtask

endclass