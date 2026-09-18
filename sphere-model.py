from mergexp import *

net = Network('single-node')

n0 = net.node('n0',
    proc.cores == 32,
    memory.capacity == gb(32),
)

experiment(net)
