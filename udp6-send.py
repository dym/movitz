#! /usr/bin/env python
######################################################################
## 
##    Copyright (C) 2001-2002, 
##    Department of Computer Science, University of Tromsø, Norway.
## 
##    For distribution policy, see the accompanying file COPYING.
## 
## Filename:      udp6-send.py
## Description:   Send a simple (IPv6) UDP packet
## Author:        Frode Vatvedt Fjeld <frodef@acm.org>
## Created at:    Sun Mar 10 20:20:11 2002
##                
## $Id: udp6-send.py,v 1.1 2004/01/13 11:04:59 ffjeld Exp $
##                
######################################################################

import sys,time,socket

if len (sys.argv) != 4:
    print "Usage: udp6-send <host> <port> <data>"
    sys.exit (1);

host = sys.argv[1]
port = sys.argv[2]
data = sys.argv[3]

mtu  = 1400
packets = (len (data) / mtu) + 1

# print "host:", host, "port:", port, "data:", data

af, socktype, proto, canonname, sa = \
    socket.getaddrinfo(host, port, socket.AF_UNSPEC, socket.SOCK_DGRAM)[0]
s = socket.socket (af, socktype, proto)
s.connect (sa)
for i in range (packets):
    print "sending packet", i, ".."
    s.send ("%d %d %s" % (i+1, packets, data[i*mtu:min(i*mtu+mtu, len (data))]))
    time.sleep (0.1)
s.close ()

