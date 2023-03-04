set border lw 2
set grid lw 1.25 lt 1 lc "grey"
set key right bottom
set key font ",12"
set key box lw 1 width -2 height 1
set xtics font ",12"
set ytics font ",12" 
# set ylabel "Time" font ",17"
# set xlabel "Dimension" font ",17"


set style line 1 dt 4 pt 2 ps 1.5 lw 2 lc "black" # gp
set style line 2 dt 5 pt 7 ps 1.1 lw 1.8 lc "orange"  # relative couveignes
set style line 3 dt 2 pt 6  lw 1.5 ps 1 lc "olive"   # relative couveignes : norm

set logscale y

file_couv_pari(prime) = sprintf('../data/couveignes_fixed_root_%s_pari', prime)
file_couv_padic(prime) = sprintf('../data/couveignes_fixed_root_%s_padic', prime)
file_couv_nfroots(prime) = sprintf('../data/couveignes_fixed_root_%s_nfroots', prime)
figure_crt(prime) = sprintf("figures/couveignes_fixed_root_%s.png", prime)


do for [PRIME in "5 7 23"] {
    plot file_couv_nfroots(PRIME) u 2:3 ls 1 w p title "Pari/Gp nfroots",\
         file_couv_pari(PRIME) u 2:11 ls 2 w p title "Alg. 5",\
	 file_couv_pari(PRIME) u 2:5 ls 3 w p title "Relative norm in Alg. 5",\
         
    set terminal pngcairo
    set output figure_crt(PRIME)
    replot
}
