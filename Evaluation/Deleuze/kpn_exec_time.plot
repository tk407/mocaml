unset title
set key bottom right
set xlabel 'Last number < 10^x'
set ylabel 'Time (s)'
set logscale y
unset logscale x
set term post eps enhanced color fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "kpn_exec_times.eps" 
set size 1.,1.

plot "kpn_cont_data_clean_realtime.txt" using log10(1):2 with lp title 'cont', \
"kpn_dlcont_data_clean_realtime.txt" using log10(1):2 with lp title 'dlcont', \
"kpn_mcon_data_clean_realtime.txt" using log10(1):2 with lp title 'mcon', \
"kpn_promise_data_clean_realtime.txt" using log10(1):2 with lp title 'promise', \
"kpn_sys_data_clean_realtime.txt" using log10(1):2 with lp title 'sys', \
"kpn_tramp_data_clean_realtime.txt" using log10(1):2 with lp title 'tramp', \
"kpn_vm_data_clean_realtime.txt" using log10(1):2 with lp title 'vm', \
"kpn_lwt_data_clean_realtime.txt" using log10(1):2 with lp title 'lwt'

set term post eps enhanced mono fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "kpn_exec_times_bw.eps" 
replot


unset title
set key top left
set xlabel 'Last number < 10^x'
set ylabel 'Memory (words)'
unset logscale xy
set term post eps enhanced color fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "kpn_mem.eps" 

plot "kpn_cont_data_clean_mem.txt" using log10(1):2 with lp title 'cont', \
"kpn_dlcont_data_clean_mem.txt" using log10(1):2 with lp title 'dlcont', \
"kpn_mcon_data_clean_mem.txt" using log10(1):2 with lp title 'mcon', \
"kpn_promise_data_clean_mem.txt" using log10(1):2 with lp title 'promise', \
"kpn_sys_data_clean_mem.txt" using log10(1):2 with lp title 'sys', \
"kpn_tramp_data_clean_mem.txt" using log10(1):2 with lp title 'tramp', \
"kpn_vm_data_clean_mem.txt" using log10(1):2 with lp title 'vm', \
"kpn_lwt_data_clean_mem.txt" using log10(1):2 with lp title 'lwt'

set term post eps enhanced mono fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "kpn_mem_bw.eps" 
replot

unset logscale xy
set term post eps enhanced color fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "kpn_ratio_mcon_cont.eps" 
plot "< paste kpn_cont_data_clean_realtime.txt kpn_mcon_data_clean_realtime.txt" using log10(1):($4/$2) with lp title 'mcon vs cont', \
"< paste kpn_dlcont_data_clean_realtime.txt kpn_mcon_data_clean_realtime.txt" using log10(1):($4/$2) with lp title 'mcon vs dlcont', \
"< paste kpn_promise_data_clean_realtime.txt kpn_mcon_data_clean_realtime.txt" using log10(1):($4/$2) with lp title 'mcon vs promise', \
"< paste kpn_tramp_data_clean_realtime.txt kpn_mcon_data_clean_realtime.txt" using log10(1):($4/$2) with lp title 'mcon vs tramp', \
"< paste kpn_vm_data_clean_realtime.txt kpn_mcon_data_clean_realtime.txt" using log10(1):($4/$2) with lp title 'mcon vs vm', \
"< paste kpn_lwt_data_clean_realtime.txt kpn_mcon_data_clean_realtime.txt" using log10(1):($4/$2) with lp title 'mcon vs lwt', \
"< paste kpn_sys_data_clean_realtime.txt kpn_mcon_data_clean_realtime.txt" using log10(1):($4/$2) with lp title 'mcon vs sys'

set term post eps enhanced mono fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "kpn_ratio_mcon_cont_bw.eps" 
replot

unset title
set key bottom right
set xlabel 'Last number < 10^x'
set ylabel 'Time (s)'
set logscale y
unset logscale x
set term post eps enhanced color fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "kpn_exec_times_opt.eps" 
set size 1.,1.

plot "kpn_cont_opt_data_clean_realtime.txt" using log10(1):2 with lp title 'cont', \
"kpn_dlcont_opt_data_clean_realtime.txt" using log10(1):2 with lp title 'mcon', \
"kpn_mcon_opt_data_clean_realtime.txt" using log10(1):2 with lp title 'mcon', \
"kpn_promise_opt_data_clean_realtime.txt" using log10(1):2 with lp title 'promise', \
"kpn_sys_opt_data_clean_realtime.txt" using log10(1):2 with lp title 'sys', \
"kpn_tramp_opt_data_clean_realtime.txt" using log10(1):2 with lp title 'tramp', \
"kpn_lwt_opt_data_clean_realtime.txt" using log10(1):2 with lp title 'lwt'

set term post eps enhanced mono fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "kpn_exec_times_opt_bw.eps" 
replot


unset title
set key top left
set xlabel 'Last number < 10^x'
set ylabel 'Memory (words)'
unset logscale xy
set term post eps enhanced color fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "kpn_mem_opt.eps" 

plot "kpn_cont_opt_data_clean_mem.txt" using log10(1):2 with lp title 'cont', \
"kpn_dlcont_opt_data_clean_mem.txt" using log10(1):2 with lp title 'dlcont', \
"kpn_mcon_opt_data_clean_mem.txt" using log10(1):2 with lp title 'mcon', \
"kpn_promise_opt_data_clean_mem.txt" using log10(1):2 with lp title 'promise', \
"kpn_sys_opt_data_clean_mem.txt" using log10(1):2 with lp title 'sys', \
"kpn_tramp_opt_data_clean_mem.txt" using log10(1):2 with lp title 'tramp', \
"kpn_lwt_opt_data_clean_mem.txt" using log10(1):2 with lp title 'lwt'

set term post eps enhanced mono fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "kpn_mem_opt_bw.eps" 
replot

unset logscale xy
set term post eps enhanced color fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "kpn_ratio_mcon_cont_opt.eps" 
plot "< paste kpn_cont_opt_data_clean_realtime.txt kpn_mcon_opt_data_clean_realtime.txt" using log10(1):($4/$2) with lp title 'mcon vs cont', \
"< paste kpn_promise_opt_data_clean_realtime.txt kpn_mcon_opt_data_clean_realtime.txt" using log10(1):($4/$2) with lp title 'mcon vs promise', \
"< paste kpn_dlcont_opt_data_clean_realtime.txt kpn_mcon_opt_data_clean_realtime.txt" using log10(1):($4/$2) with lp title 'mcon vs dlcont', \
"< paste kpn_tramp_opt_data_clean_realtime.txt kpn_mcon_opt_data_clean_realtime.txt" using log10(1):($4/$2) with lp title 'mcon vs tramp', \
"< paste kpn_lwt_opt_data_clean_realtime.txt kpn_mcon_opt_data_clean_realtime.txt" using log10(1):($4/$2) with lp title 'mcon vs lwt', \
"< paste kpn_sys_opt_data_clean_realtime.txt kpn_mcon_opt_data_clean_realtime.txt" using log10(1):($4/$2) with lp title 'mcon vs sys'

set term post eps enhanced mono fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "kpn_ratio_mcon_cont_opt_bw.eps" 
replot
