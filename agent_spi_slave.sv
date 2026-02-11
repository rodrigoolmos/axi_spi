interface spi_if;
    
    logic sclk;
    logic mosi;
    logic miso;
    logic cs_n;

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

    task write_byte();
        logic [7:0] data;
        data = buffer_read.pop_front();
        $display("Slave sending: 0x%02X", data);
        wait(!spi_s_if.cs_n);
        for (int i=0; i<8; ++i) begin
            if (spi_cfg.cpha) begin
                spi_s_if.miso = spi_cfg.msb_first ? data[7-i] : data[i];
                @(negedge spi_s_if.sclk);
            end else begin
                spi_s_if.miso = spi_cfg.msb_first ? data[7-i] : data[i];
                @(posedge spi_s_if.sclk);
            end
        end
    endtask

    task write();
        wait(!spi_s_if.cs_n);
        fork
            forever write_byte();
            wait(spi_s_if.cs_n);
        join_any

        disable fork;
    endtask

    task read_byte();
        logic [7:0] data;

        wait(!spi_s_if.cs_n);
        for (int i=0; i<8; ++i) begin
            if (spi_cfg.cpha) begin
                @(negedge spi_s_if.sclk);
                data = spi_cfg.msb_first ? {data[6:0], spi_s_if.mosi} : {spi_s_if.mosi, data[7:1]};
            end else begin
                @(posedge spi_s_if.sclk);
                data = spi_cfg.msb_first ? {data[6:0], spi_s_if.mosi} : {spi_s_if.mosi, data[7:1]};
            end
        end
        $display("Slave received: 0x%02X", data);
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

endclass