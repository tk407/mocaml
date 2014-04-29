/* highlight-reach.g */
BEG_G {
    node_t n0 = node($,ARGV[0]);
    $tvroot = node($,ARGV[0]);
    if (ARGC == 2) $tvtype = TV_fwd;
    else $tvtype = TV_rev;
}
N {
    $tvroot = NULL;
    color="green";
    style="filled";
}
E {
    color="green";
}
