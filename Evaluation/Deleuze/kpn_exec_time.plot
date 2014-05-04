unset title
set key bottom right
set xlabel 'Last number < 10^x'
set ylabel 'Time (s)'
set logscale y
unset logscale x
set term post eps enhanced color fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200"
set output "kpn_exec_times.eps" 
set size 1.,1.

plot "kpn_cont_data_clean_realtime.txt" using log10(1):2 with lp title 'cont', \
"kpn_mcon_data_clean_realtime.txt" using log10(1):2 with lp title 'mcon', \
"kpn_promise_data_clean_realtime.txt" using log10(1):2 with lp title 'promise', \
"kpn_sys_data_clean_realtime.txt" using log10(1):2 with lp title 'sys', \
"kpn_tramp_data_clean_realtime.txt" using log10(1):2 with lp title 'tramp', \
"kpn_vm_data_clean_realtime.txt" using log10(1):2 with lp title 'vm'

set term post eps enhanced mono fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200"
set output "kpn_exec_times_bw.eps" 
replot


unset title
set key top left
set xlabel 'Last number < 10^x'
set ylabel 'Memory (words)'
unset logscale xy
set term post eps enhanced color fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200"
set output "kpn_mem.eps" 

plot "kpn_cont_data_clean_mem.txt" using log10(1):2 with lp title 'cont', \
"kpn_mcon_data_clean_mem.txt" using log10(1):2 with lp title 'mcon', \
"kpn_promise_data_clean_mem.txt" using log10(1):2 with lp title 'promise', \
"kpn_sys_data_clean_mem.txt" using log10(1):2 with lp title 'sys', \
"kpn_tramp_data_clean_mem.txt" using log10(1):2 with lp title 'tramp', \
"kpn_vm_data_clean_mem.txt" using log10(1):2 with lp title 'vm'

set term post eps enhanced mono fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200"
set output "kpn_mem_bw.eps" 
replot
