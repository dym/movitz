######################################################################
## 
##    Copyright (C) 2003-2004, 
##    Department of Computer Science, University of Tromsoe, Norway.
## 
##    For distribution policy, see the accompanying file COPYING.
## 
## Filename:      web-update.sh
## Description:   
## Author:        Frode Vatvedt Fjeld <frodef@acm.org>
## Created at:    Mon Nov 10 11:54:33 2003
##                
## $Id: web-update.sh,v 1.1 2004/04/18 12:32:56 ffjeld Exp $
##                
######################################################################

WWW="common-lisp.net:public_html"
SCP="/usr/local/bin/scp2"

# ${SCP} doc/movitz.html ${WWW}
${SCP} los0-image ${WWW}/files/los0.img
${SCP} COPYING doc/ChangeLog doc/report/movitz.pdf grub-bootloader/grub-bootloader.img ${WWW}/files

