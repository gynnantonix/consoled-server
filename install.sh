#! /bin/sh

destdir=/usr

echo -n "Shutting down consoled"
service consoled stop
echo ""

if [ ! -r Makefile ];
then
	echo "Building Makefile"
	perl Makefile.PL
fi

echo "Installing consoled & system configuration updates"

install sbin/consoled $destdir/sbin/consoled
install etc/logrotate.d/L1 /etc/logrotate.d/L1
install etc/init.d/consoled /etc/init.d/consoled

if ( ! `grep --silent L1.log /etc/syslog.conf` );
then
   echo "Updating syslog configuration"
   echo -e '\n# L1 daemon output\nlocal1.*\t\t\t/var/log/L1.log' >>/etc/syslog.conf;
   kill -HUP `cat /var/run/syslogd.pid`
fi

echo "Adding consoled to init system"
chkconfig --add consoled

echo -n "Starting consoled..."
service consoled start

echo ""
echo "Done."
