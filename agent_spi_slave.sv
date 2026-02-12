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

    function automatic bit sample_on_posedge(bit cpol, bit cpha);
        bit leading_is_pos = (cpol == 0);
        return (cpha == 0) ? leading_is_pos : !leading_is_pos;
    endfunction

    task write_byte();
        logic [7:0] data;
        bit sample_pos;
        bit update_pos;

        data = buffer_read.pop_front();

        sample_pos = sample_on_posedge(spi_cfg.cpol, spi_cfg.cpha);
        update_pos = !sample_pos;

        spi_s_if.miso <= spi_cfg.msb_first ? data[7] : data[0];
        @(edge spi_s_if.sclk);

        for (int i = 0; i < 8; i++) begin
            spi_s_if.miso <= spi_cfg.msb_first ? data[7-i] : data[i];

            if (update_pos) @(posedge spi_s_if.sclk);
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

endclass