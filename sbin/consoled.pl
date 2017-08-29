#! /usr/bin/perl -w

## @file
# Perl-based implementation of a DeMonIC server.
#
# Uses multiplexed-i/o via IO::Select (an interface to the system select(3) call)
# and timeout-protected or non-blocking i/o to ensure responsiveness.
#
# Output operations are only done when we are signalled that the other end of the
# connection is ready to recieve.  This minimizes the amount of time we spend blocked
# trying to write to clients and devices, since we always know that they're ready to
# recieve what we're sending when we go to send.
#
# Input operations are done the same way -- we only try to read from clients and
# stream devices which IO::Select has indicated are ready to be read from.
#
# @author Catherine Mitchell


use strict;
use warnings;
use Sys::Syslog qw(:standard :macros);
use Sys::Hostname;
use Unix::PID;
use Time::HiRes qw(usleep ualarm);
use Proc::Daemon;
use Pod::Usage;
use IO::Handle;
use IO::Socket;
use IO::Socket::UNIX;
use IO::Socket::INET;
use IO::Select;
use Device::SerialPort;
use Net::Telnet;
use Fcntl qw(:flock);
use Switch;
use Carp;
use JSON;
use Getopt::Long;

our $VERSION = 'DEVELOPMENT';
our $ID = '$Id$';


# - - - - - - - - - - - CONFIGURATION DATA - - - - - - - - - - -

# Lock file which prevents multiple instances of this program from running
use constant PIDFILE => '/var/run/consoled.pid';
# User and group under which to run
use constant UID => 'nobody';
use constant GID => 'nobody';
# Syslog facility to use
use constant SYSLOG_FACILITY => LOG_LOCAL1;
# Name of this program -- prefixed to each line we send to syslog
use constant SYSLOG_TAG => 'consoled';
# Directory where we can find this system's PCFG
use constant PCFG_DIR => '/pcfg';
# Directory where we can find the Multi-host group information
use constant MH_GROUP_DIR => '/path/to/multihost_group_confs';
# Number of seconds between checking our PCFG for changes
# (and re-reading if it's changed)
use constant PCFG_REFRESH_INTERVAL => 600;
# number of seconds child process should wait before sending HUP signal
# to server process in case of device failure
use constant DEVICE_RETRY_INTERVAL => 60;
# number of consecutive times to try and re-init a device which didn't come
# up at configuration time
use constant MAX_DEVICE_INIT_RETRIES => 5;
# number of seconds to wait after doing a "PORT x LOGOUT" command
# on an SCS (it needs time to clear clients from the indicated port)
use constant SCS_PORT_LOGOUT_WAIT_TIME => 3;
# number of seconds to wait before failing on a log-in attempt
use constant SCS_LOGIN_TIMEOUT => 5;
# number of seconds to pause after issuing a command to an SCS which causes it to update its DB
use constant SCS_RECONFIGURE_WAIT_TIME => 5;
# regex which describes telnet prompt for SCS, and other SCS settings
use constant SCS_PROMPT_REGEX => '/> /';
use constant SCS_TELNET_USER => 'Admin';
use constant SCS_TELNET_PASSWORD => 'password';
# default OA access tokens (used in cases where PCFG doesn't define them for a
# particular OA)
use constant OA_PROMPT_REGEX => '/> $/';
use constant OA_USER => 'admin';
use constant OA_PASS => 'password';
# port number on which console stream server will listen
use constant LISTEN_PORT => 29168;
# number of seconds to wait between tries at getting a lock on a serial device
use constant DEV_LOCK_RETRY_INTERVAL => 5;
# window (in seconds) for getting a lock on a serial device
use constant DEV_LOCK_WINDOW => 300;
# protocol level
use constant DEMONIC_VERSION_MAJ => 0;
use constant DEMONIC_VERSION_MIN => 51;
# Internet EOL (cr+nl)
use constant EOL => "\015\012";
# amount of time which a client has to respond before we assume it's dead
use constant CLIENT_PING_TIMEOUT => 50;
# interval between client aliveness checks
use constant CLIENT_PING_INTERVAL => 60;
# interval between printing of "** marker **" messages to our log file
# (in seconds)
use constant MARKER_INTERVAL => 600;
# name of program to open on a pipe to serve dummy devices
use constant DUMMY_DEV_PROG => '/tmp/dummy.dev.prog';
# a map of serial device prefixes to appropriate baud rates for them
my %baudrate = (
  'CLI' => 57600,
  'SEP' => 9600,
  'HBA' => 19200
);

# - - - - - - - - - - - RUNTIME VARS - - - - - - - - - - -

# our configuration file
my $pcfg_file;
# SCS password
my $SCS_pass;
# SCS user-name
my $SCS_user;
# base directory to which PCFG files are relative
my $PCFG_base_dir = PCFG_DIR;
# last time PCFG was checked for changes
my $last_pcfg_refresh = 0;
# modification time of last PCFG we read
my $last_pcfg_mtime = 0;
# flag indicating whether or not we're paying attention to storage target designations
my $using_storage_targets = 0;
# list of storage target IDs which we're supposed to watch
my @storage_targets;
# array of OA definitions
#   [oa_idx] ->
#      {'IP'}     OA IP
#      {'user'}   (optional) OA username (will contain OA_USER if none given)
#      {'pass'}   (optional) OA password (will contain OA_PASS if none given)
my @OA;
# non-zero if and while we're shutting down
my $shutting_down = 0;
# non-zero during the period of time between which we receive notification
# to re-configure and when we're done re-configuring
my $re_starting = 0;
# non-zero between the time that start() has finished and stop() has not
# yet been called
my $running = 0;
# if zero, no process has been spawned to HUP us.	If non-zero, contains
# the PID of the process spawned to send us a HUP.
my $hup_scheduled = 0;
# time at which we'll send out the next round of pings to clients
my $ping_time = -1;
# time at which we'll print the next marker message
my $marker_time;
# time at which we commenced operations
my $start_time = time;
# vector of handles to service when they're ready to be read
my $read_vec;
# vector of handles to service when they're ready to be written
my $write_vec;
# vector of handles to service in case they raise an exception
my $exception_vec;
# handle for our listening socket
my $listen_socket;
# a hash of outgoing data buffers by IO handle, one for each
# active device or client handle; each buffer is a list of
# individual transactions to send
my %outbox;
# A hash of incoming data buffers by IO handle.
# These buffers are scalars into which incoming data is placed
# until a complete message is assembled.
my %inbox;
# statistics for each known device by the name of the stream
# they serve
# {stream_name}
#	  {'failed_init_count'} = # of consecutive failed inits for this device
#	  {'exception_count'} = # number of exceptions seen on this device
my %device_statistics;
# should we create the DUMMY device?
my $create_dummy = 0;
# a count of the number of streams using the dummy device
my $streams_using_dummy = 0;
# did we create the script used to fuel the dummy device?
my $we_created_dummy_script = 0;
# should we only provide the DUMMY device?
my $fake_it = 0;
# hash of configuration variables for multihost test cell (may be empty)
my %multihost_conf;
# are we the master host for the test cell?
my $we_are_master_host = 1;
# hash of IPs of SCSes which we've told to share connections
my %configured_scs;


# - - - - - - - - - - - CLIENT DATA - - - - - - - - - - -

# A list of all clients ever seen (stores the unique symbol assigned to
# each connection we accept by Perl).	Will contain both connected and
# no-longer connected clients.
my @clients;
# a mapping of client handle (the UID assigned to each connection object
# by Perl) to the client's index in @clients.  Only connected clients are
# in this mapping
my %client_ID;
# a mapping of client handle to the IP:port from which the client is
# connecting (same rules as %client_ID apply)
my %client_IP;
# a hash of client handles to the last time when a client responded to
# a ping request
my %last_heard_from;


# - - - - - - - - - - - STREAM DATA - - - - - - - - - - -

# mapping of stream name (e.g. CLIA) to device (e.g. /dev/ttyUSB1), plus
#	 connection state and buffers for the device
# {stream_name} ->
#	  {'device_type'} = "SCS"|"RS232"
#	  ...device-specific parameters...
#	  {'handle'} = reference to connection handle
#	  {'close_handler'} = reference to subroutine to call in order to close
#								 this device (sub needs stream name as param)
my %stream_devices;
# mapping from device handle to the name of the stream which that device serves
my %streamdev_handles;
# map from stream name to a list of client IDs listening to that stream
my %stream_listeners;
# map from stream name to the ID of the client which has write permissions
# for that stream (if no such client exists for a stream, there won't be
# a key for that stream here)
my %stream_writer;


# - - - - - - - - - - - PROTOTYPES - - - - - - - - - - -

# server control functions
sub usage(;$);
sub getSysname();
sub checkEnvironment();
sub get_configuration(\%$);
sub start();
sub re_start();
sub stop();
sub hup_me();

# i/o functions
sub service_io();
sub writeToHandle($$);
sub writeToStream($$$);
sub broadcast($;@);
sub sendMessage($$);
sub streamExists($);
sub processStreamIncoming($);
sub processStreamOutgoing($);
sub processStreamException($);
sub processClientIncoming($);
sub processClientOutgoing($);
sub processClientException($);

# DeMonIC-specific functions
sub makeMessage(;%);
sub decodeMessage($);
sub msgIsDemonic($);
sub processMessage($$);

sub addClient($);
sub removeClient($);
sub pingClients();
sub clientIsAlive($);
sub reportErrorToClient($;@);
sub sendPingRequest($);
sub sendPingResponse($);
sub sendStreamStatus($$);
sub sendGeneralStatus($);
sub addClientToStream($$;$);
sub removeClientFromStream($$);

# device drivers (each has an open_ and close_ function)
# see start() for how these are used
sub open_scs($);
sub close_scs($);
sub open_dev($);
sub close_dev($);
sub open_icbaydev($);
sub close_icbaydev($);
sub open_dummy($);
sub close_dummy($);

# error-handling and logging functions
sub printLog(@);
sub printDbg(@);
sub printErr(@);
sub termErr(@);

# - - - - - - - - - - - - MAIN - - - - - - - - - - - -
MAIN:
{
	my $sysname;
	my $help = 0;
	my $version = 0;

	# get the name of the system we're running on (assume it's the same
	# as the host-name if SYSTEM isn't set in the environment)
	$sysname = getSysname();
	
	GetOptions( 'p|pcfg=s'     => \$pcfg_file,
	            'b|pcfg-dir=s' => \$PCFG_base_dir,
	            'h|help!'      => \$help,
	            'v|version!'   => \$version,
	            'fake-it!'     => \$fake_it,
	            'dummy!'       => \$create_dummy )
	  or pod2usage();

	usage(0) if ($help);
	
	if ($version)
	{
		print("$VERSION\n");
		exit(0);
	}
	
	# fake-it implies create_dummy
	if ($fake_it)
	{
		$create_dummy = 1;
		$pcfg_file = '/dev/null';
	}

	if (@ARGV)
	{
		# get the PCFG file to use from the command line, or use the default
		$pcfg_file = shift(@ARGV) || PCFG_DIR . "/$sysname.pcfg";
	}

	# set up syslog for logging so that this program name is prefixed
	# to each entry
	openlog(SYSLOG_TAG, "ndelay", SYSLOG_FACILITY) or die("Can't start syslog: $!");

	termErr("PCFG file %s doesn't exist", $pcfg_file) unless (-e $pcfg_file);
	termErr("PCFG file %s can't be read", $pcfg_file) unless (-r $pcfg_file);
	
	# daemonize
	Proc::Daemon::Init();

	# make sure that we're clear to run
	checkEnvironment();

#	# set up an END block to remove our PID file
#	# (we needed to wait to do this until after we forked -- otherwise
#	# the original process would have unlinked the file on exit)
#	END { ( -e PIDFILE ) && unlink(PIDFILE); }

	# log the fact that we're starting
	syslog(LOG_NOTICE, 'Starting up');
	syslog(LOG_INFO, '%s %s %s', SYSLOG_TAG, $VERSION, $ID);
	syslog(LOG_INFO, 'Using "%s" as PCFG file', $pcfg_file);

	# set up signal handlers
	$SIG{HUP}  = 'handle_sighup';
	$SIG{TERM} = 'handle_deathsig';
	$SIG{CHLD} = 'handle_kid';

	# set up the time when we should print our first log marker message
	$marker_time = time + MARKER_INTERVAL;

	# initialize SCS credentials with defaults
	$SCS_user = SCS_TELNET_USER;
	$SCS_pass = SCS_TELNET_PASSWORD;

	# start all configured services
	start();

	# enter select loop
	while (! $shutting_down)
	{
		# if any PCFGs have changed since last time we read ours, re-configure
		if ((($last_pcfg_refresh + PCFG_REFRESH_INTERVAL) >= time) &&
		    ((stat(PCFG_DIR))[9] != $last_pcfg_mtime))
		{
			printDbg('Configuration change detected');
			$last_pcfg_refresh = time;
			$last_pcfg_mtime = (stat(PCFG_DIR))[9];
			$re_starting = 1;
		}

		# handle requests for re-start and/or PCFG re-read interval
		if ($re_starting)
		{
			re_start();
#			broadcast_status();
			$re_starting = 0;
			$last_pcfg_refresh = time;
		}

		# handle clients and services
		service_io();

		# print our log marker if it's time to do so
		if (time >= $marker_time)
		{
			syslog(LOG_INFO, '** marker **');
			$marker_time = time + MARKER_INTERVAL;
		}

		# send out pings if it's time to do so and pings are enabled
		if (($ping_time > -1) && (time >= $ping_time))
		{
			pingClients();
			$ping_time = time + CLIENT_PING_INTERVAL;
		}
	}

	# it's time to shut down, so do it
	stop();

	syslog(LOG_INFO, 'Exiting.');
	exit(0);
}
# - - - - - - - - - - - END MAIN - - - - - - - - - - -


## @cmethod void start()
# Reads the PCFG file and configures any streams which need starting
# or stopping, and sets up listening socket.
# Also sets up vectors of i/o handles for use with Select().
sub start()
{
	my %new_dev_map;
	my @streams_to_stop;	 # list of running streams to stop
	my @streams_to_start; # list of streams to start
	my $streams_started = 0; # count of streams actually started
	my $streams_stopped = 0; # count of streams actually stopped
	my $key;
	my $stream;
	my $devcount;
	my $sysname;

	# get the name by which we're known in the PCFG
	$sysname = getSysname();

	# if we're already running, close the listening socket temporarily
	# while we re-configure; we'll open it back up once we're configured
	if ($running)
	{
		printLog('Closing listening socket during re-configuration');
		$read_vec->remove($listen_socket);
		$write_vec->remove($listen_socket);
		$exception_vec->remove($listen_socket);
		$listen_socket->close();
	}

	printLog('Configuring...');

	# if we're re-configuring, these will already be set up
	if (! $running)
	{
		# set up vectors for Select
		if (! ( ($read_vec = new IO::Select) &&
			($write_vec = new IO::Select) &&
			($exception_vec = new IO::Select) ) )
		{
			termErr('Unable to create Select object: %s', $!);
		}
	}
	
	# re-initialize configuration variables which are set from the PCFG
	%multihost_conf = ();
	@storage_targets = [];
	$using_storage_targets = 0;

	$devcount = get_configuration(%new_dev_map, $pcfg_file);

	if (! defined($devcount))
	{
		printErr('Failure reading device configuration from %s', $pcfg_file);
		$shutting_down = 1;
		return(1);
	}
	elsif ($devcount != 0)
	{
		syslog(LOG_ERR, 'Failure getting device configuration');
		$shutting_down = 1;
		return(1);
	}

	# if there's multi-host configuration information...	
	if (exists($multihost_conf{'MULTIHOSTMASTER'}))
	{
		printDbg('Master host for test cell is [%s]; we\'re [%s]',
		         $multihost_conf{'MULTIHOSTMASTER'},
		         $sysname);
		
		# If we're not running on the master host for the test cell, we shouldn't
		# open (or keep open) any devices.  If we were previously the master host,
		# print a message saying that we're not the master host and delete our device
		# configuration; this will cause any open devices to be closed.
		if ($multihost_conf{'MULTIHOSTMASTER'} eq $sysname)
		{
			if (! $we_are_master_host)
			{
				$we_are_master_host = 1;
				printLog("We've become the master host for this test cell; " .
						 "opening resources and throttling up.");
			}
			
			# if there's a multi-host group configured for this test cell, read the PCFGs of all hosts
			# in the test cell, meld it with ours, and use the resulting super device-map
			if (exists($multihost_conf{'MULTIHOSTGROUP'}))
			{
				%new_dev_map = (%new_dev_map, readMHGroupPCFGs($multihost_conf{'MULTIHOSTGROUP'}));
			}
		}
		else
		{
			# if we were the master host before, note the change in state and clear out the hash
			# we use for tracking which SCSes we've configured for automatic port sharing
			if ($we_are_master_host)
			{
				$we_are_master_host = 0;
				%configured_scs = ();
				printLog("We are no longer the master host for this test cell; " .
						 "releasing resources and going idle.");
			}
			
			%new_dev_map = ();
		}
	}
	else
	{
		printLog("No multi-host group defined for this test cell; " .
				 "assuming this is the only host and not reading other PCFGs.");
	}

	# Generate list of streams to start by comparing the stream names in the new device map
	# to the ones in the map of currently-running streams.
	# Fold new entries into existing dev map.
	foreach $key (keys(%new_dev_map))
	{
		if (! exists($stream_devices{$key}))
		{
			push(@streams_to_start, $key);
			$stream_devices{$key} = $new_dev_map{$key};
		}
	}

	# Generate list of streams to stop by comparing list of running streams to new device map.
	# The routine for stopping streams will clean up the dev map entry of stopped streams,
	# so don't delete them yet.
	foreach $key (keys(%stream_devices))
	{
		push(@streams_to_stop, $key) if (! exists($new_dev_map{$key}));
	}

	# start new streams
	foreach $stream (@streams_to_start)
	{
		my $open_ok = 0;

		# select the handler function to use based on the type of device attached to this service
		if ($stream_devices{$stream}{'device_type'} eq 'RS232')
		{
			$open_ok = open_dev($stream);
		}
		elsif ($stream_devices{$stream}{'device_type'} eq 'SCS')
		{
			$open_ok = open_scs($stream);
		}
		elsif ($stream_devices{$stream}{'device_type'} eq 'ICBAYDEV')
		{
			$open_ok = open_icbaydev($stream);
		}
		elsif ($stream_devices{$stream}{'device_type'} eq 'DUMMY')
		{
			$open_ok = open_dummy($stream);
		}
		else
		{
			printErr('Unable to start service for unknown device type "%s"',
				$stream_devices{$stream}{'device_type'});
		}

		# if the device came up ok, initialize it; otherwise, delete it from our
		# stored configuration so that we don't report it as an active stream,
		# and hope that someone HUPs us after it's fixed
		if ($open_ok)
		{
			$streams_started++;
			initialize($stream);
			# the stream started ok, so delete the count of times it failed to start
			delete($device_statistics{$stream}{'failed_init_count'});
			# tell any clients which are already connected that this stream is
			# back online
			broadcast(makeMessage('identifier' => 'data',
			                      'stream'     => $stream,
			                      'data'       => "Stream $stream online\n"),
						 @{$stream_listeners{$stream}});
		}
		else
		{
			my $re_inits;

			delete($stream_devices{$stream});
			# make sure our failed init count is initilized to zero the first
			# time we use it for this stream
			$device_statistics{$stream}{'failed_init_count'} = 0
			  unless (exists($device_statistics{$stream}{'failed_init_count'}));
			$re_inits = ($device_statistics{$stream}{'failed_init_count'} += 1);
			if ($re_inits < MAX_DEVICE_INIT_RETRIES)
			{
				printErr('Device serving stream %s failed to start; re-trying.', $stream);
				hup_me();
			}
			elsif ($re_inits == MAX_DEVICE_INIT_RETRIES)
			{
				printErr('Device serving stream %s has failed to start too many times; giving up on it.', $stream);
				printErr('Once error has been fixed, please shut down and re-start consoled.');
			}
			else
			{
				printErr('Device serving stream %s has permanent failures and will not be started.', $stream);
			}
		}
	}

	# stop no-longer-configured streams
	foreach $stream (@streams_to_stop)
	{
		# select the handler function to use based on the type of device attached to this service
		if ($stream_devices{$stream}{'device_type'} eq 'RS232')
		{
			close_dev($stream);
		}
		elsif ($stream_devices{$stream}{'device_type'} eq 'SCS')
		{
			close_scs($stream);
		}
		elsif ($stream_devices{$stream}{'device_type'} eq 'ICBAYDEV')
		{
			close_icbaydev($stream);
		}		
		elsif ($stream_devices{$stream}{'device_type'} eq 'DUMMY')
		{
			close_dummy($stream);
		}

		$streams_stopped++;
		cleanup($stream);
	}

	# register an END block which will assure that if we die or exit, streams are stopped
	# cleanly (won't work on a forced kill, of course) [note that the END block only gets
	# set up once, at compile time -- this won't be set every time this function is called]
	END { $running && stop() };

	printLog('Configuration complete.  Stream stats: %d started, %d stopped.',
				$streams_started,
				$streams_stopped);

	# create a non-blocking socket
	$listen_socket = IO::Socket::INET->new(
	  Proto         => 'tcp',
	  LocalPort     => LISTEN_PORT,
	  Listen        => SOMAXCONN,
	  ReuseAddr     => 1,
	  Blocking      => 0
	);
	termErr('Unable to create listener socket: %s', $!) unless ($listen_socket);

	# add listener socket to handles we want to know about when they're ready
	# to be read or they have an exception
	$read_vec->add($listen_socket);
	$exception_vec->add($listen_socket);

	printLog('Listening for connections on port %d', LISTEN_PORT);

	# set the running semaphore
	$running = 1;
}

## @cmethod void re_start()
# Re-configures the server.
sub re_start()
{
	syslog(LOG_INFO, 'Re-configuring...');
	start();
	syslog(LOG_INFO, 'Re-configuration complete.');
}

## @cmethod void stop()
# Stops the server.
# Shuts down all services and closes remaining client connections.
sub stop()
{
	my @stoplist;
	my @connected_clients;
	my $stream;
	my $client;

	# prevent us from being called twice
	return unless ($running);
	$running = 0;

	printLog('Stopping services');

	# close listen socket
	$listen_socket->close();

	@stoplist = keys(%stream_devices);

	# stop services
	foreach $stream (@stoplist)
	{
		# select the handler function to use based on the type of device attached to this service
		if ($stream_devices{$stream}{'device_type'} eq 'RS232')
		{
			close_dev($stream);
		}
		elsif ($stream_devices{$stream}{'device_type'} eq 'SCS')
		{
			close_scs($stream);
		}
		elsif ($stream_devices{$stream}{'device_type'} eq 'ICBAYDEV')
		{
			close_icbaydev($stream);
		}
		elsif ($stream_devices{$stream}{'device_type'} eq 'DUMMY')
		{
			close_dummy($stream);
		}

		cleanup($stream);
	}
}

## @cmethod void hup_me()
# Forks a child process which waits DEVICE_RETRY_INTERVAL seconds
# and then sends us a HUP signal so that we re-configure.
sub hup_me()
{
	my $parent_pid = $$;
	my $kidpid;

	# don't request another HUP if we've already got one in the pipe
	return if ($hup_scheduled);

	printLog('Scheduling a re-configuration in %d seconds', DEVICE_RETRY_INTERVAL);

	if (($kidpid = fork()) == 0)
	{
		sleep(DEVICE_RETRY_INTERVAL);
		kill('HUP', $parent_pid);
		exit(0);
	}

	$hup_scheduled = $kidpid;
}

## @cmethod void service_io()
# Processes all service and client handles which are ready.
sub service_io()
{
	my $read_ref;
	my $write_ref;
	my $excp_ref;
	my $handle;

	# select on our vectors of filehandles, with a timeout of 2 seconds so
	# that if there's nothing to do for our services or clients we don't
	# block other activities
	($read_ref, $write_ref, $excp_ref) = IO::Select::select($read_vec,
															$write_vec,
															$exception_vec,
															2000);

	# process exceptions first
	foreach $handle (@$excp_ref)
	{
		if ($handle == $listen_socket)
		{
			printLog("Exception raised on listener socket");
		}
		# if the handle with the exception is a stream device handle...
		elsif (exists($streamdev_handles{$handle}))
		{
			processStreamException($handle);
		}
		else
		{
			processClientException($handle);
		}
	}

	# process handles with data ready for reading
	foreach $handle (@$read_ref)
	{
		if ($handle == $listen_socket)
		{
			addClient($handle->accept());
		}
		elsif (exists($streamdev_handles{$handle}))
		{
			processStreamIncoming($handle);
		}
		else
		{
			processClientIncoming($handle);
		}
	}

	# process handles which are ready for writing
	foreach $handle (@$write_ref)
	{
		# if the client hung up before we got around to it here,
		# the hangup will have been caught by processClientIncoming
		# and the connection will have been closed; check for that
		# here before trying to process the handle
		next unless (exists($client_IP{$handle}) ||
						 exists($streamdev_handles{$handle}));

		# if there's no data for the handle, de-register it
		if ($#{$outbox{$handle}} < 0)
		{
			$write_vec->remove($handle);
			next;
		}

		if (exists($streamdev_handles{$handle}))
		{
			processStreamOutgoing($handle);
		}
		else
		{
			processClientOutgoing($handle);
		}
	}
}

## @cmethod boolean writeToHandle($handle, $data)
# Sets up the given data to be written to the given handle once
# that handle reports ready to be written.
# Doesn't actually write the data to the handle -- only sets
# up for the data to be written once the handle is ready.
#
# @param handle A reference to a handle to which to write
# @param data The data to write to the given handle
#
# @return True on success, False otherwise.
sub writeToHandle($$)
{
	my $handle = shift;
	my $data = shift;

	push(@{$outbox{$handle}}, $data);

	$write_vec->add($handle);

	return(1);
}

## @cmethod void writeToStream($client, $stream, $data)
# Attempt to write data to a stream for a client.
#
# If another client has write permission, an error will
# be returned to the originating client.	If this client
# holds write permission or no client holds write permission,
# the write will be attempted.
#
# @param client client handle
# @param stream stream name
# @param data data to write to stream
sub writeToStream($$$)
{
	my $client = shift;
	my $stream = shift;
	my $data = shift;
	my $response;

	$response = makeMessage('identifier' => 'ok',
									'command' => 'write',
									'stream' => $stream);

	# if there is no writer, or this client is the writer, we can
	# do the write
	if ((! exists($stream_writer{$stream})) || ($stream_writer{$stream} == $client))
	{
		writeToHandle($stream_devices{$stream}{'handle'}, $data);
	}
	else
	{
		$response->{'identifier'} = 'fail';
		$response->{'error'} = 'No write permission';
	}

	sendMessage($client, $response) if ($client && $client->opened() && $client->connected());
}

## @cmethod void broadcast($message_ref, @clients)
# Broadcasts the given message.	If no client list is supplied,
# the message is sent to all clients.	If a client list is
# supplied, the message is sent to the given clients.
#
# @note Doesn't check the validity of the message.
#
# @param message_ref a reference to the message to send
# @param clients an optional list of recieving clients
sub broadcast($;@)
{
	my $msg_ref = shift;
#	my @client_list = shift || @clients;
	my @client_list = @_;
	my $client;

	@client_list = @clients unless ($#client_list >= 0);
	
	foreach $client (@client_list)
	{
		next unless (defined($client));

		sendMessage($client, $msg_ref);
	}
}


## @cmethod boolean streamExists($stream)
# Tests whether the given stream exists or not.
#
# @param stream Name of stream to test
sub streamExists($)
{
	my $stream = shift;

	return(0) unless ( exists($stream_devices{$stream}) &&
	                   exists($stream_devices{$stream}{'handle'}) );

	return(1);
}

## @cmethod void processStreamIncoming($handle)
# Processes the data coming in from the given device handle.
#
# @param handle The handle from which to read data.
sub processStreamIncoming($)
{
	my $handle = shift;
	my $data;
	my $stream;
	my $sysread_ret;

	$stream = $streamdev_handles{$handle};

	$sysread_ret = sysread($handle, $data, 200);

	# if sysread returns 0, it's equivalent to an EOF.	 If sysread
	# returns undef, there was an error reading the device.	Either
	# way, we'll assume that the device has hung up;
	# shut it down and flag for a re-start
	if ((! defined($sysread_ret)) || ($sysread_ret == 0))
	{
		printLog('Device serving stream %s has hung up', $stream);
		printDbg('sysread() said: %s', $!) if (! defined($sysread_ret));
		# call the close method for this type of handle (set by
		# the open method)
		&{$stream_devices{$stream}{'close_handler'}}($handle)
		  if exists($stream_devices{$stream}{'close_handler'});
		# clean up all references to this handle so that it will be
		# garbage-collected
		cleanup_handle($handle);
		delete($stream_devices{$stream});
		# flag for a re-configuration
		$re_starting = 1;
		# set up a message to be sent to all subscribers of this stream
		# indicating that it has shut down
		$data = "Device serving stream $stream has gone offline\n";
	}

	# if there wasn't a complete line in that transmission, data
	# will be empty and we've got nothing to do
#	return unless (length($data) > 0);

	broadcast(makeMessage('identifier' => 'data',
	                      'stream'     => $stream,
	                      'data'       => $data,
	                      'time'       => time),
	          @{$stream_listeners{$stream}}
	         );
}

## @cmethod void processStreamOutgoing($handle)
# Processes any outgoing data for the given handle.
#
# Once all data waiting for the handle has been sent, the handle is
# removed from the list of handles to test for write-readiness so that
# we aren't called again until writeToHandle sets up new data to be
# written to the handle and adds it back to the aforementioned list.
#
# @param handle The handle to write to
sub processStreamOutgoing($)
{
	my $handle = shift;
	my $data;

	return unless exists($outbox{$handle});

	$data = shift(@{$outbox{$handle}});

	# print our data to the device, making sure to protect
	# ourselves from a blocking operation by using an alarm to
	# break out of the i/o block if it occurs
	eval
	{
		local $SIG{ALRM} = sub { die "PSO_alarm\n" };
		ualarm(200);
		print($handle $data);
		alarm(0);
	};
	if ($@ eq "PSO_alarm\n")
	{
		printErr('Timed out while writing to %s', $streamdev_handles{$handle});
	}
}

## @cmethod void processStreamException($handle)
# Handles exceptions generated on device handles.
# Just logs the exception, really.
#
# @param handle Device handle
sub processStreamException($)
{
	my $handle = shift;

	printDbg('Exception generated on stream %s', $streamdev_handles{$handle});
	$handle->clearerr();
}

## @cmethod void processClientIncoming($handle)
# Processes data coming in from a client.
#
# Data is assumed to a DeMonIC message, in part or whole.  It isn't
# interpreted until a whole message is recieved.  Data is initially
# concatenated onto the client's buffer in %inbox.	 The buffer is then
# scanned for a complete message.  If there's a complete message, the
# message is read out of the buffer and processed.	 Only one message
# is processed at a time in order to avoid starving other requests.
#
# @note Assumes that there is data waiting and that a read will not block.
#
# @param handle Client connection handle
sub processClientIncoming($)
{
	my $handle = shift;
	my $data;
	my $raw_message;
	my $msg_ref;
	my $read_ret;

	# read the handle
	$read_ret = sysread($handle, $data, 10000);
	# if the read didn't return anything, assume we got EOF and
	# remove the client
	if (! (defined($data) && defined($read_ret) && ($read_ret > 0)))
	{
		printLog('Client %d has hung up', $client_ID{$handle});
		printDbg('sysread() says: %s', $!) if ($!);
		removeClient($handle);
		return;
	}

	# add the data to the client's incoming data buffer
	$inbox{$handle} .= $data;

	# see if we've got a complete messsage; if we don't, we're done
	return unless ($inbox{$handle} =~ s/^([^\r]+)(\r\n)+//);

	# we found a complete message; interpret it.
	$raw_message = $1;
	chomp($raw_message);

	if (! ($msg_ref = decodeMessage($raw_message)))
	{
		reportErrorToClient($handle, "Couldn't decode message << $raw_message >>");
		return;
	}
	if (! msgIsDemonic($msg_ref))
	{
		reportErrorToClient($handle, "Message format error: $!");
		return;
	}

	if (! processMessage($handle, $msg_ref))
	{
		reportErrorToClient($handle, "Error interpreting message: $!");
		return;
	}
	
	printDbg('Recieved message from client %d', $client_ID{$handle});
}

## @cmethod void procesClientOutgoing($handle)
# Sends a single message to a single client.
# The first message in the client's %outbox queue is sent.
#
# Doesn't test to see if there ARE any messages -- assumes
# that there are messages to send.
#
# @param handle Handle to the client connection
sub processClientOutgoing($)
{
	my $handle = shift;
	my $data;

	printDbg('Sending message to client %d', $client_ID{$handle});

	$data = shift(@{$outbox{$handle}}) . EOL;

	eval
	{
		local $SIG{ALRM} = sub { die "PCO_alarm\n" };
		ualarm(200);
		syswrite($handle, $data);
		alarm(0);
	};
	if ($@ eq "PCO_alarm\n")
	{
		printErr('Timed out while writing to client %d (%s)',
					$client_ID{$handle}, $client_IP{$handle});
	}
}

## @cmethod void processClientException($handle)
# Processes exceptions raised on client connection handles.
# Actually just logs the fact that there was an exception.
sub processClientException($)
{
	my $handle = shift;

	printDbg('Exception raised by client %d (%s)',
				$client_ID{$handle}, $client_IP{$handle});
	$handle->clearerr();
}

## @cmethod void open_scs($stream_name)
# Starts service for the indicated stream by connecting to the SCS which
# is serving that stream.
#
# Opens telnet connection to the SCS indicated in the stream's configuration
# (in %stream_devices).	 Uses the "port <x> logout" command to log-out all
# other connections from the configured SCS port and then connects to it,
# sharing it if asked.
#
# The connection handle is stored in
# $stream_devices{stream_name}->{'handle'}.
# It is also added to the vector of handles to be read ($read_vec) and the
# vector of handles to check for exceptions ($exception_vec).
#
# A reference to the routine to call to close the stream once it's finished
# is stored in:
# $stream_devices{stream_name}->{'close_handler'}
#
# @param stream_name the name of the service to start
#
# @return True on success, False otherwise
sub open_scs($)
{
	my $stream = shift;
	my $telnet;
	my $ip;
	my $port;

	# make sure that we have a complete configuration
	if (! exists($stream_devices{$stream}{'IP'}))
	{
		printErr('Configuration for SCS serving %s is missing IP address -- skipping it',
					$stream);
		return(0);
	}
	$ip = $stream_devices{$stream}{'IP'};

	if (! exists($stream_devices{$stream}{'PORT'}))
	{
		printErr('Configuration for SCS serving %s is missing port number -- skipping it',
		         $stream);
		return(0);
	}
	$port = $stream_devices{$stream}{'PORT'};
	
	# open up a telnet connection to the SCS
	$telnet = new Net::Telnet ( 'Prompt'  => SCS_PROMPT_REGEX,
	                            'Host'    => $ip,
	                            'Errmode' => 'return' );
	# check that we've got a connection
	if (! defined($telnet))
	{
		printErr('Unable to open telnet connection to the SCS at %s: %s', $ip, $!);
		return(0);
	}

	# log in
	if (! $telnet->login( 'Name'     => $SCS_user,
	                      'Password' => $SCS_pass,
	                      'Timeout'  => SCS_LOGIN_TIMEOUT))
	{
		printErr('Unable to log into SCS at %s: %s', $ip, $telnet->errmsg());
		return(0);
	}

	# before connecting to the actual stream, log into the SCS CLI and kick out 
	# anyone who's on our port
	printDbg('Clearing connections to port %d on SCS at %s', $port, $ip);
	
	if (! $telnet->print("port $port logout"))
	{
		printLog('Unable to clear connections from port %d on SCS %s', $port, $ip);
		return(0);
	}
	
	# wait for any logging-out activity
	printDbg('Waiting %d seconds for SCS to log-out connections to the port',
	         SCS_PORT_LOGOUT_WAIT_TIME);
	sleep(SCS_PORT_LOGOUT_WAIT_TIME);
	
	if (! exists($configured_scs{$ip}))
	{
		$configured_scs{$ip} = 1;

		# tell the SCS to automatically share any connections (just do it instead of asking)
		printDbg('Configuring SCS to automatically share ports');
	
		if (! $telnet->print("server share auto"))
		{
			printLog('Error configuring automatic sharing of ports; continuing');
			$configured_scs{$ip} = 0;
		}
		else
		{
			printDbg('Waiting %d seconds for SCS to reconfigure', SCS_RECONFIGURE_WAIT_TIME);
			sleep(SCS_RECONFIGURE_WAIT_TIME);
		}

		printDbg('Disabling SCS CLI timeout');
		if (! $telnet->print("server cli timeout=0"))
		{
			printLog('Error configuring CLI timeout to 0');
			$configured_scs{$ip} = 0;
		}
		else
		{
			printDbg('Waiting %d seconds for SCS to reconfigure', SCS_RECONFIGURE_WAIT_TIME);
			sleep(SCS_RECONFIGURE_WAIT_TIME);
		}

		printDbg('Disabling SCS port timeouts');
		if (! $telnet->print("port all set timeout=0"))
		{
			printLog('Error configuring port timeouts to 0');
			$configured_scs{$ip} = 0;
		}
		else
		{
			printDbg('Waiting %d seconds for SCS to reconfigure', SCS_RECONFIGURE_WAIT_TIME);
			sleep(SCS_RECONFIGURE_WAIT_TIME);
		}
	}
	
	# close the CLI session and end the telnet session if the SCS doesn't get to it first
	$telnet->print("QUIT");
	sleep(1);
	$telnet->close() if ($telnet && $telnet->opened());

	## connect to the external port for our stream
	## (TCP port 3000 + SCS internal port #)
	$port = $stream_devices{$stream}{'PORT'} + 3000;

	printDbg('Opening stream %s via SCS at %s port %d', $stream, $ip, $port);

	# open up a telnet connection to the SCS, but directly to the device port
	# (don't supply a prompt because the only place we're going to be prompted is at login)
	$telnet = new Net::Telnet ( 'Prompt'  => '/.*/',
	                            'Host'    => $ip,
	                            'Port'    => $port,
	                            'Errmode' => 'return' );
	                            
	# check that we've got a connection
	if (! defined($telnet))
	{
		printErr('Unable to open connection: %s', $!);
		return(0);
	}

	# log in
	if (! $telnet->login('Name'     => $SCS_user,
	                     'Password' => $SCS_pass,
	                     'Timeout'  => SCS_LOGIN_TIMEOUT ))
	{
		printErr('Unable to log into SCS at %s: %s', $ip, $telnet->errmsg());
		return(0);
	}

	# share the session, if asked
	if (! $telnet->print("s"))
	{
		printErr('Unable to share port %d on SCS %s', $port, $ip);
		return(0);
	}

	# set writes to the device to be un-buffered
	$telnet->autoflush(1);

	# save reference to function to be called when it's time to close
	# this device
	$stream_devices{$stream}{'close_handler'} = \&close_scs;
	# save a reference to the handle so it doesn't go out of scope
	$stream_devices{$stream}{'handle'} = $telnet;

	return(1);
}

## @cmethod void close_scs($stream_name)
# Stops service for the indicated SCS-served stream.
# Closes the telnet connection to the SCS and logs the service stop.
#
# @param stream_name the name of the service to stop
sub close_scs($)
{
	my $stream = shift;
	my $handle;

	return unless exists($stream_devices{$stream});

	printDbg('Closing stream %s', $stream);
	
	$handle = $stream_devices{$stream}{'handle'};

	# escape into the CLI with <ctrl>+D, and then issue QUIT to close the SCS connection
	writeToHandle($handle, pack('h', '0x04'));
	processStreamOutgoing($handle);
	writeToHandle($handle, "QUIT\n");
	processStreamOutgoing($handle);

	$handle->close() if ($handle && $handle->opened());
	$handle->close() if ($handle && $handle->opened());
}

## @cmethod boolean open_dev($stream_name)
# Starts service for the indicated direct-connect serial device.
# Obtains an exclusive advisory lock on the serial device, opens
# it, and logs that we've opened the device.
#
# @param stream_name the name of the stream whose device we are to open
#
# @return True on success, False on failure
sub open_dev($)
{
	my $stream = shift;
	my $serial_control;
	my $device;
	my $dev_handle;
	my $timeout;
	my @blockers;	# list of processes which are blocking us from opening device
	
	$device = $stream_devices{$stream}{'device'};
	termErr('Missing device path for stream %s', $stream) unless defined($device);
	
	printLog('Opening stream %s via %s', $stream, $device);
	
	@blockers = `lsof -F pc $device`;
	
	# @blockers is a list of processes which have our monitoring port open.
	# Each blocking process has two entries in @blockers: the first is the
	# process number, the second is the process name.
	while ($#blockers > 0)
	{
		my $proc_name;
		my $proc_id;
	
		shift(@blockers) =~ /^p(\d+)/;
		$proc_id = $1;
		shift(@blockers) =~ /^c(\S+)/;
		$proc_name = $1;
		printLog("$proc_name found blocking $device; killing it");
		kill(9, $proc_id);
	}
	
	if (! ($serial_control = Device::SerialPort->new($device)))
	{
	  printErr("Couldn't create TTY object for device [$device]");
	  return(0);
	}
	if (! ($serial_control->baudrate($baudrate{substr($stream, 0, 3)})))
	{
	  printErr("Couldn't set baud-rate for $device: $!");
	  return(0);
	}
	if (! $serial_control->parity('none'))
	{
	  printErr("Couldn't set parity for $device");
	  return(0);
	}
	if (! $serial_control->databits(8))
	{
	  printErr("Couldn't set number of data-bits for $device");
	  return(0);
	}
	if (! $serial_control->stopbits(1))
	{
	  printErr("Couldn't set number of stop-bits for $device");
	  return(0);
	}
	if (! $serial_control->handshake('none'))
	{
	  printErr("Couldn't set handshake for $device");
	  return(0);
	}
	if (! $serial_control->write_settings())
	{
	  printErr("Couldn't commit settings to $device");
	  return(0);
	}
	
	# sleep a couple of seconds
	sleep(2);
	
	# open device
	if (! (open($dev_handle, '+>', $device)))
	{
	  printErr("Couldn't open %s: %s", $device, $!);
	  return(0);
	}
	
	# attempt to get an exclusive lock on the monitored device; if the first
	# attempt fails, keep trying for a set amount of time before giving up
	$timeout = time + DEV_LOCK_WINDOW;
	while ((time < $timeout) && (! flock($dev_handle, LOCK_EX|LOCK_NB)))
	{
	  sleep(DEV_LOCK_RETRY_INTERVAL);
	}
	# if the timer's run down, we know that we weren't successful in getting a
	# lock, so say something, clean up, and exit.
	if (time >= $timeout)
	{
	  close($dev_handle);
	  printErr('Timed out trying to get a lock on %s', $device);
	  return(0);
	}
	
	$stream_devices{$stream}{'handle'} = $dev_handle;
	$stream_devices{$stream}{'serial_obj'} = $serial_control;
	$stream_devices{$stream}{'close_handler'} = \&close_dev;
	
	return(1);
}

## @cmethod void close_dev($stream_name)
# Closes the direct-attached serial device associated with a given stream.
#
# @param stream_name The stream whose direct-attached serial device we
# are to close.
sub close_dev($)
{
	my $stream = shift;
	my $serial_ref;
	my $handle;

	return unless ( exists($stream_devices{$stream}) &&
	                exists($stream_devices{$stream}{'serial_obj'}) );

	$handle = $stream_devices{$stream}{'handle'};
	$serial_ref = $stream_devices{$stream}{'serial_obj'};

	flock($handle, LOCK_UN);
	close($handle);

	$serial_ref->close();
}

## @cmethod void open_icbaydev($stream_name)
# Starts service for the indicated stream by connecting to the indicated OA
# and opening the indicated Musket log stream.
#
# Opens telnet connection to the OA indicated in the stream's configuration
# (in %stream_devices).	 Uses connection info in that OA's parameter hash
# (as read from the OA lines in the PCFG), using default username & password
# if not otherwise supplied.  From the OA, opens a connection to the Musket's
# Interconnect Bay (ICBAY).  
#
# The connection handle is stored in
# $stream_devices{stream_name}->{'handle'}.
# It is also added to the vector of handles to be read ($read_vec) and the
# vector of handles to check for exceptions ($exception_vec).
#
# A reference to the routine to call to close the stream once it's finished
# is stored in:
# $stream_devices{stream_name}->{'close_handler'}
#
# @param stream_name the name of the service to start
#
# @return True on success, False otherwise
sub open_icbaydev($)
{
	my $stream = shift;
	my $telnet;
	my $oa_idx;
	my $ip;
	my $icbay;
	my $user;
	my $pass;

	# make sure that we have an OA to talk to
	if (! exists($stream_devices{$stream}{'OA'}))
	{
		printErr('Configuration for stream %s invalid: no OA index supplied',
		         $stream);
		return(0);
	}
	# get the index for the OA we're supposed to talk to
	$oa_idx = $stream_devices{$stream}{'OA'};

	# make sure that we've been pointed to a valid OA entry
	if (! defined($OA[$oa_idx]))
	{
		printErr('Configuration for stream %s is invalid: OA index [%d] doesn\'t exist',
		         $stream, $oa_idx);
		return(0);
	}
	
	$ip = $OA[$oa_idx]->{'IP'};
	$user = $OA[$oa_idx]->{'user'};
	$pass = $OA[$oa_idx]->{'pass'};

	if (! exists($stream_devices{$stream}{'ICBAY'}))
	{
		printErr('Configuration for stream %s is missing ICBay number -- skipping it',
		         $stream);
		return(0);
	}
	$icbay = $stream_devices{$stream}{'ICBAY'};

	printDbg('Opening stream %s via OA %s, ICBAY %d', $stream, $ip, $icbay);

	# open up a telnet connection to the SCS
	$telnet = new Net::Telnet ( 'Prompt'  => OA_PROMPT_REGEX,
	                            'Host'    => $ip,
	                            'Errmode' => 'return' );

	# check that we've got a connection
	if (! defined($telnet))
	{
		printErr('Unable to open telnet connection to the SCS at %s: %s', $ip, $!);
		return(0);
	}

	# log in
	if (! $telnet->login($user, $pass))
	{
		printErr('Unable to log into OA at %s: %s', $ip, $telnet->errmsg());
		return(0);
	}

	# clear sessions from the port
	if (! $telnet->print("clear icbay session $icbay"))
	{
		printWarn('Unable to clear sessions from ICBay %d on OA %s', $icbay, $ip);
		return(0);
	}
	
	# connect to the monitored port or back out
	if (! $telnet->print("connect interconnect $icbay"))
	{
		printErr('Unable to connect to ICBay %d on OA %s', $icbay, $ip);
		return(0);
	}
	
	# wait for OA to print message about pressing ctrl+_ to exit session...
	sleep(1);
	
	# send a newline in order to actually connect to Musket
	$telnet->print(' ');

	# set writes to the device to be un-buffered
	$telnet->autoflush(1);

	# save reference to function to be called when it's time to close
	# this device
	$stream_devices{$stream}{'close_handler'} = \&close_icbaydev;
	# save a reference to the handle so it doesn't go out of scope
	$stream_devices{$stream}{'handle'} = $telnet;

	return(1);
}

## @cmethod void close_icbaydev($stream_name)
# Stops service for the indicated OA-served stream.
#
# Closes the OA->Musket (ICBay) connection with <ctrl>+_ (0x1F) followed
# by 'D' (to disconnect), and then closes the OA session with 'quit'.
#
# @param stream_name the name of the service to stop
sub close_icbaydev($)
{
	my $stream = shift;
	my $handle;

	return unless exists($stream_devices{$stream});

	printDbg('Closing stream %s', $stream);
	
	$handle = $stream_devices{$stream}{'handle'};

	# to close a connection to an ICBay and get back to the OA CLI,
	# we issue <ctrl>+_ (which is 0x1F) to get back to the CLI, and then
	# say 'D' to disconnect from the device.
	writeToHandle($handle, pack('h', '0x1F'));
	processStreamOutgoing($handle);
	writeToHandle($handle, "D\n");
	processsStreamOutgoing($handle);
	
	# finally, to close our CLI session cleanly, we say "QUIT"
	writeToHandle($handle, "quit\n");
	processStreamOutgoing($handle);

	$handle->close() if ($handle && $handle->opened());
}

## @cmethod void open_dummy($stream_name)
# Starts service for a dummy stream.
# Dummy streams are served by a process whose output is read on a
# file handle.  This process outputs the date (using the 'date'
# program) every one second.
# Each dummy stream gets its own invocation of the process.
#
# @param stream_name the name of the stream which is to be served
#   by the dummy device
#
# @return True on success, False on failure
sub open_dummy($)
{
	my $stream = shift;
	my $handle;
	
	# make a dummy dev script if it's not there
	if (! -x DUMMY_DEV_PROG)
	{
		printLog("Creating DUMMY_DEV_PROG");
		$we_created_dummy_script = 1;
		open(DSH, ">", DUMMY_DEV_PROG);
		print(DSH "#!/bin/bash\n#created by consoled\nwhile true; do printf '%s\r\n' \"`date`\"; sleep 1; done;\n");
		close(DSH);
		chmod(0777, DUMMY_DEV_PROG);
	}
	
	# open our dummy dev script on a pipe to serve this dummy device
	if (! open($handle, DUMMY_DEV_PROG . " |"))
	{
		printErr("Error opening stream $stream as a dummy device: $!");
		return(0);
	}
	
	$stream_devices{$stream}{'handle'} = $handle;
	$stream_devices{$stream}{'close_handler'} = \&close_dummy;
	$streams_using_dummy += 1;
	
	return(1);
}

## @cmethod void close_dummy($stream_name)
# Stops service for a dummy device.
# Closes the pipe on which the date-generating process is opened for
# the indicated stream.
#
# @param stream_name the dummy stream to close
sub close_dummy($)
{
	my $stream = shift;
	my $handle;
	
	$handle = $stream_devices{$stream}{'handle'};
	close($handle);
	
	# if we created the script which fuels dummy devices and there are no
	# more such devices using it, delete the script
	if (($streams_using_dummy == 0) && ($we_created_dummy_script == 1))
	{
		printLog("Unlinking DUMMY_DEV_PROG");
		unlink(DUMMY_DEV_PROG);
	}
}

## @cmethod void initialize($stream_name)
# Performs any actions necessary to "wake up" a given stream device.
# Generally, this means sending a couple of newlines to the device.
# Also, the handle for the device is added to the vectors of handles
# passed to select() so that we'll be signalled for read/write
# readyness the first time they reach that state.
#
# @param stream_name The stream we are to initialize.
sub initialize($)
{
	my $stream = shift;
	my $handle;

	$handle = $stream_devices{$stream}{'handle'};

	# add the handle to the three select() vectors
	$read_vec->add($handle);
	$write_vec->add($handle);
	$exception_vec->add($handle);

	# add the handle to our map of handles to the name of the stream
	# each one serves
	$streamdev_handles{$handle} = $stream;

	# set up an empty list of listeners
	# we don't set up writer because the condition no-writer-for-stream
	# is signalled by the lack of an entry in %stream_listeners for the stream
	$stream_listeners{$stream} = [] unless (exists($stream_listeners{$stream}));

	# set up i/o buffers for handle
	$inbox{$handle} = "";
	$outbox{$handle} = [];

	writeToHandle($handle, "\n\n");
}

## @cmethod void cleanup($stream_name)
# Performs any post-close cleanup required after a stream has been closed.
# Deletes run-time storage and configuration for the indicated stream.
#
# @param stream_name The name of the stream after which we're cleaning up
sub cleanup($)
{
	my $stream = shift;
	my $handle;
	my $position;

	$handle = $stream_devices{$stream}{'handle'} || termErr("No handle found for $stream");

	cleanup_handle($handle);

	# delete client tracking entries for this stream
	delete($stream_listeners{$stream});
	delete($stream_writer{$stream}) if exists($stream_writer{$stream});

	# delete stream configuration
	delete($stream_devices{$stream});
}

## @cmethod void cleanup_handle($handle)
# Deletes all references to the given handle.
#
# @param handle the handle to delete
sub cleanup_handle($)
{
	my $handle = shift;

	# de-register stream from select() handles
	$read_vec->remove($handle);
	$write_vec->remove($handle);
	$exception_vec->remove($handle);

	# delete the handle from the map of stream handles to the devices they serve
	delete($streamdev_handles{$handle});

	# delete i/o buffers
	delete($inbox{$handle});
	delete($outbox{$handle});
}




## @cmethod boolean get_configuration(%output, $config_file)
# Fills out the given hash with a map of stream names to stream devices, taken from
# the indicated PCFG file.
#
# Any STORAGE_TARGET definitions are added to the global storage_target array.  This
# array should be reset outside-of and before this function if target definitions are
# not to be persistent across configuration reads.
#
# Any MULTIHOST keys are added to the global %multihost_conf hash.  This hash should be
# reset outside-of and before this function if such keys are not to be persistent.
#
# @param output a reference to a hash which should be filled with the configuration
# @param config_file the configuration to parse into %output
#
# @return 0 on success and non-zero on failure.
sub get_configuration(\%$)
{
	my $devmap_ref = shift;
	my $new_pcfg = shift;
	my @interesting_lines;
	my $retval = 0;
	my $line;
	my $lineno = 0;

	if (! -r $new_pcfg)
	{
		syslog(LOG_WARNING, 'Can\'t read PCFG file "%s"', $new_pcfg);
		return(-2);
	}

	# clear out the given hash
	foreach (keys(%$devmap_ref))
	{
		delete($devmap_ref->{$_});
	}

	# if we're faking it, skip reading any PCFG
	if ($fake_it)
	{
		printDbg('Not reading PCFG file -- running in fake-it mode');
	}
	else
	{
		if (! open(PCFG, $new_pcfg))
		{
			$! = sprintf('Unable to open PCFG file %s: %s', $new_pcfg, $!);
			return(-1);
		}
		
		# find all lines which aren't commented-out
		@interesting_lines = grep { /^[^#]/ } <PCFG>;
		close(PCFG);
	}
	
	# if we're to set up the DUMMY device, inject it into the configuration here
	if ($create_dummy)
	{
		push(@interesting_lines, "DUMMY1     consoled_dummy_dev");
		push(@interesting_lines, "DUMMY2     consoled_dummy_dev");
	}
	
	# now that we have only the lines we want, pull them into the map of stream names
	# stream devices
	foreach $line (@interesting_lines)
	{
		my $stream_name;
		my $device_type;
		my $parameter;
		my $setting;
	
		chomp($line);
		
		# pull any comments off the end of the line
		$line =~ s/\#.*$//;
		
		# keep 1-based count of lines in PCFG
		$lineno++;
		
		# skip lines which start with PDU
		if ($line =~ /^\s*(PDU_[^\s]*)/)
		{
			printDbg('Skipping %s', $1);
			next;
		}
		
		# if we've been told to only use lines which relate to certain
		# storage targets, skip lines which don't list one of the storage
		# targets we were told to watch
		if ($using_storage_targets)
		{
			my $target_number;
			
			# only pay attention to lines which list a storage target
			next unless ($line =~ /^\s*TARGET_(\d+)/);
			# get the target number
			$target_number = $1;
			# only pay attention to entries which list one of the storage
			# targets we're meant to pay attention to
			next unless (grep { $_ == $target_number } @storage_targets);
		}

		# see if this line describes an SCS-based monitoring device
		if ($line =~ /([^\s]+)_SCS_([\w\d]+)\s+([^\s]+)$/)
		{
			$stream_name = $1;
			$device_type = 'SCS';
			$parameter = $2;
			$setting = $3;
		}
		# see if this describes a directly-connected RS232 device
		elsif ($line =~ /([^\s]+)_RS232\s+([^\s]+)$/)
		{
			# direct-connect serial ports have only one parameter: the device
			# to open.
			$stream_name = $1;
			$device_type = 'RS232';
			$parameter = 'device';
			$setting = $2;
		}
		# see if this line describes a Musket device
		elsif ($line =~ /(\S+)_ICBAYDEV_([^_\s]+)\s+(\S+)\s*$/)
		{
			$stream_name = $1;
			$device_type = 'ICBAYDEV';
			$parameter = $2;
			$setting = $3;
		}
		# see if this line describes an OA
		elsif ($line =~ /^OA_(\d+)\s+(\S+)(.*)/)
		{
			my $oa_idx = $1;
			my $oa_ip = $2;
			my $params = $3;
			my $user;
			my $pass;
			
			# make sure that the index is valid ({Z} > 0)
			if (int($oa_idx) != $oa_idx)
			{
				printErr("In file $new_pcfg, line $lineno:");
				printErr("Invalid OA configuration: OA index [$oa_idx] is not an integer >= 0");
				next;
			}
			
			$OA[$oa_idx] = { 'IP' => $oa_ip };

			# process optional params, if any
			if (defined($params))
			{
				($user, $pass) = split(/\s+/, $params);
				
				$OA[$oa_idx]->{'user'} = defined($user) ? $user : OA_USER;
				$OA[$oa_idx]->{'pass'} = defined($pass) ? $pass : OA_PASS;
			}
			
			printDbg('Got OA configuration: IDX(%02d) IP(%15s) USER(%15s) PASS(%s)',
			         $oa_idx,
			         $OA[$oa_idx]->{'IP'},
			         $OA[$oa_idx]->{'user'},
			         $OA[$oa_idx]->{'pass'}
			        );

			# this isn't a stream configuration, so go to the next line
			next;
		}
		# see if this line tells us to include another PCFG -- if so,
		# recurse and fold in the results
		elsif ($line =~ /^\s*INCLUDE_PCFG\s+([^\s]+)/)
		{
			my $other_pcfg_name = "$PCFG_base_dir/" . $1;
			my %other_pcfg_contents;
			
			printDbg('Including PCFG file "%s"', $other_pcfg_name);
			
			if (get_configuration(%other_pcfg_contents, $other_pcfg_name) != 0)
			{
				syslog(LOG_WARNING, 'Unable to include PCFG file "%s"', $other_pcfg_name);
				next;
			}
			
			printDbg('Inclusion OK.');
			
			# meld the contents of the included PCFG with the one we're reading
			%$devmap_ref = (%$devmap_ref, %other_pcfg_contents);
			next;
		}
		# pick up MULTIHOST keys
		elsif ($line =~ /^\s*(MULTIHOST\S*)\s+(\S+)/)
		{
			$multihost_conf{$1} = $2;
			printDbg('Got Multihost key [%s] = [%s]', $1, $2);
			next;
		}
		# accept SCS_USER and SCS_PASS keys
		elsif ($line =~ /^\s*SCS_USER\s+(.*)/)
		{
			$SCS_user = $1;
			printDbg('Using SCS user "%s"', $SCS_user);
			next;
		}
		elsif ($line =~ /^\s*SCS_PASS\s+(.*)/)
		{
			$SCS_pass = $1;
			printDbg('Using SCS password "%s"', $SCS_pass);
			next;
		}	
		# handle lists of storage targets to watch
		elsif ($line =~ /^\s*STORAGE_TARGETS\s+([\d\s]+)/)
		{
			my $target_list = $1;
			my @these_targets;
			my %all_targets;
			my $target;
			
			$using_storage_targets = 1;
			
			@these_targets = split(/[\s,]+/, $target_list);
			printDbg('Got list of storage targets to watch: %s', join(',', @these_targets));
			
			# make a list of unique storage targets by combining our current list of
			# targets with the one we just recieved
			foreach $target (@storage_targets, @these_targets)
			{
				$all_targets{$target} = 1;
			}
			
			@storage_targets = sort keys(%all_targets);
			
			next;
		}
		# line describes a consoled-generated dummy device
		elsif ($line =~ /^\s*(\S+)\s+consoled_dummy_dev\s*$/)
		{
			$stream_name = $1;
			$device_type = 'DUMMY';
		}
		else
		{
			next;
		}
		
		printDbg('Recognized %s device in "%s"', $device_type, $line);
		printDbg('Interpreted as DEVICE(%8s) PARAM(%8s) SETTING(%4s) STREAM(%s)',
		         $device_type, $parameter, $setting, $stream_name);
		
		# standardize stream names as upper-case
		$stream_name = uc($stream_name);
			
		# since some device configurations take multiple keys, make sure that the device
		# name doesn't already exist in the map before inserting it
		if (! exists($devmap_ref->{$stream_name}))
		{
			my %newdevice = ( 'device_type' => $device_type );
			$devmap_ref->{$stream_name} = \%newdevice;
		}
		
		# store the parameter and setting
		$devmap_ref->{$stream_name}{$parameter} = $setting;
	}
	return($retval);
}

## @cmethod %devmap readMHGroupPCFGs()
# Assembles device map containing all of the log devices for all of the hosts in this
# host's test cell.
#
# The Multi-host group file is used to find out which hosts are in this test cell.  That file
# is an XML file, and really we should use an XML reader such as XML::Simple to read it.
# However, we simply scan for the <host>...</host> entries and assemble a list of hostnames
# from them.  The names of stations are collected from that list of hostnames; it is assumed
# that station name is the host name.
#
# The PCFG for each station is then read and melded with the others to form a union of all
# log device configurations for the cell.
#
# @return a hash containing all of the log devices configured in the host's test cell.
sub readMHGroupPCFGs($)
{
	my $mh_group_name = shift || croak("No multi-host group specified");
	my %new_dev_map;
	my @file;
	my @cell_hosts;
	my $multihost_group_file = MH_GROUP_DIR . "/$mh_group_name.xml";
	my $line;
	my $host;
	
	if (! -d MH_GROUP_DIR)
	{
		printWarn("Can't see multihost group configuration directory (%s); not reading other PCFGs.",
		          MH_GROUP_DIR);
		return(%new_dev_map);
	}
	
	if (! open(MHGC, $multihost_group_file))
	{
		printWarn("Unable to read multihost group configuration file (%s); not reading other PCFGS.",
		          $multihost_group_file);
		return(%new_dev_map);
	}
	@file = <MHGC>;
	close(MHGC);
	
	foreach $line (@file)
	{
		next unless ($line =~ /<host>\s*([^<]+)\s*<\/host>/);
		push(@cell_hosts, $1);
	}
	
	printLog("Reading PCFGs for hosts " . join(',', @cell_hosts));
	
	# for each hostname, figure out what its PCFG file is called and read that file
	foreach $host (@cell_hosts)
	{
		my $hostpcfg = PCFG_DIR . "/$host.pcfg";
		my %host_dev_map;
		my $devcount;
		
		$devcount = get_configuration(%host_dev_map, $hostpcfg);
		
		%new_dev_map = (%new_dev_map, %host_dev_map)
		  if (defined($devcount) && ($devcount == 0));
	}
	
	return(%new_dev_map);
}


## @cmethod boolean checkEnvironment()
# Makes sure that we're clear to run.
# Checks that:
# - we're not already running (via PID file mechanism)
# Sets up PID file.
#
# @return True if we're clear to run, and dies if there's a problem.
sub checkEnvironment()
{
	my $PID;
	my $pidReturn;

	# set up a new pid-diddler
	$PID = new Unix::PID;

	# try to set up a .pid file
	$pidReturn = $PID->pid_file_no_unlink(PIDFILE);

	# if there were errors trying to create the PID file, we can't run.
	if (! (defined($pidReturn) && $pidReturn))
	{
		if (defined($PID->get_errstr()) && ($PID->get_errstr() =~ /\S+/))
		{
			termErr("Unable to create PID file " . PIDFILE . ": " . $PID->get_errstr());
		}
		termErr("Unable to create PID file " . PIDFILE);
	}
}

## @cmethod void addClient($handle)
# Adds the indicated client to our list of clients.
# Sets up the ping timer whenever the first active client is added.
#
# @param handle Client's connection handle
sub addClient($)
{
	my $client = shift;
	my $port;
	my $ipaddr;

	# only add the connection if we were given a defined value
	return unless (defined($client));

	# if this is the first active client, set up the ping timer
	$ping_time = time + CLIENT_PING_INTERVAL if (keys(%client_ID) == 0);

	# get the port and IP address from which the client is connecting
	($port, $ipaddr) = sockaddr_in($client->connected());

	# add client to the list of all clients seen
	push(@clients, $client);
	# store its ID and IP
	$client_ID{$client} = $#clients;
	$client_IP{$client} = sprintf('%s:%d', inet_ntoa($ipaddr), $port);

	# set up i/o buffers for client
	$inbox{$client} = "";
	$outbox{$client} = [];

	# say that we heard a ping from this client just now so that it
	# doesn't immediately get timed-out
	$last_heard_from{$client} = time;

	$read_vec->add($client);
	$write_vec->add($client);
	$exception_vec->add($client);

	printLog('Accepted client %d from %s', $client_ID{$client}, $client_IP{$client});
}

## @cmethod void removeClient($handle)
# Removes the indicated client from our current client data.
# Turns off the ping timer if there are no more connected clients.
#
# @param handle Client's connection handle
sub removeClient($)
{
	my $client = shift;
	my $stream;

	printLog('Closing connection to client %d', $client_ID{$client});

	# unsubscribe client from all streams
	foreach $stream (keys(%stream_devices))
	{
		removeClientFromStream($client, $stream);
	}

	# delete storage & remove references to client handle
	delete($client_IP{$client});
	$clients[$client_ID{$client}] = undef;
	delete($client_ID{$client});
	delete($inbox{$client});
	delete($outbox{$client});
	delete($last_heard_from{$client});

	$read_vec->remove($client);
	$write_vec->remove($client);
	$exception_vec->remove($client);

	# close connection to client
	$client->close();

	# turn off the ping timer if there aren't any more connected clients
	$ping_time = -1 if (keys(%client_IP) == 0);
}

## @cmethod hash_ref makeMessage(%fields)
# Returns a reference to a hash containing the given fields and the appropriate
# header info for the protocol in use.
# If no fields are given, the minimal valid DeMonIC message is returned.
#
# @param fields The fields to put into the message
#
# @return A hash reference to a message.
sub makeMessage(;%)
{
	my %message = @_;

	#$self->printLog("Creating message");
	$message{'version'} = (DEMONIC_VERSION_MAJ . '.' . DEMONIC_VERSION_MIN) + 0;
	return(\%message);
}

## @cmethod boolean sendMessage($recipient, %message)
# Sends the given message to the given recipient.
# Handles the JSON encoding of the message.	No validity checks are done
# on the given message.
#
# @param recipient The handle to which to send the message
# @param message the message to send
#
# @return True if we were able to send, False otherwise.
sub sendMessage($$)
{
	my $recipient = shift;
	my $msg_ref = shift;

	#$self->printLog("Sending message");
#	 return(writeToHandle($recipient, encode_json($msg_ref) . "\n"));
	return(writeToHandle($recipient, encode_json($msg_ref)));

}

## @cmethod hashref decodeMessage($raw_message)
# Decodes a JSON-encoded message.
#
# @param raw_message A complete JSON-encoded message string
#
# @return On success, a reference to a hash representing the contents of
# the given message; on failure, undef.
sub decodeMessage($)
{
	my $raw_message = shift;
	my $msg_ref;

	eval
	{
		$msg_ref = decode_json($raw_message);
	};
	if (! (defined($msg_ref) && (ref($msg_ref) eq 'HASH')))
	{
		printErr('Unable to decode message %s', $raw_message);
		return(undef);
	}
	return($msg_ref);
}

## @cmethod boolean msgIsDemonic($msgref)
# Determines whether the given message is at least a minimally-valid
# message for the DeMonIC protocol verion(s) known to this server.
#
# @param msgref Reference to hash describing message
#
# @return True if message conforms to minimal known DeMonIC message format;
#	False if it doesn't.
sub msgIsDemonic($)
{
	my $msg_ref = shift;

	# check the message's structure
	if (ref($msg_ref) ne 'HASH')
	{
		$! = "Message reference is not a hash";
		printDbg($!);
		return(0);
	}
	# make sure that there's a version field
	if (! ( exists($msg_ref->{'version'}) ) )
	{
		$! = "Message is non-conformant: no 'version' field";
		printDbg($!);
		return(0);
	}
	# make sure that the version is one we can grok
	if (! ( $msg_ref->{'version'} =~ /^(\d+)\.\d+/) &&
			( $1 <= DEMONIC_VERSION_MAJ ) )
	{
		$! = sprintf('Message is non-conformant: major version mismatch (ours=%d theirs=%d)',
						 DEMONIC_VERSION_MAJ, $1);
		printDbg($!);
		return(0);
	}
	# make sure that there's an identifier field
	if (! exists($msg_ref->{'identifier'}))
	{
		$! = "Message is non-conformant: no 'identifier' field";
		printErr($!);
		return(0);
	}

	return(1);
}

## @cmethod boolean processMessage($client, $msg_ref)
# Interprets a DeMonIC message and attempts to act on it.
#
# @note Doesn't check validity of given message; assumes that it
# conforms to known version(s) of DeMonIC message format.
#
# @param client The handle of the client which sent the message
# @param msg_ref A reference to the hash representing the message
#
# @return True if message was successfully processed; otherwise, false.
sub processMessage($$)
{
	my $client = shift;
	my $msg_ref = shift;

	# make sure identifiers are lower-case
	$msg_ref->{'identifier'} = lc($msg_ref->{'identifier'});

	# process ping-* keys
	if ($msg_ref->{'identifier'} =~ /^ping-/)
	{
		if ($msg_ref->{'identifier'} eq 'ping-request')
		{
			printLog('Responding to ping request from client %d', $client_ID{$client});
			sendMessage($client, makeMessage('identifier' => 'ping-response'));
			return(1);
		}
		elsif ($msg_ref->{'identifier'} eq 'ping-response')
		{
			delete($last_heard_from{$client});
			printDbg('Ping response recieved from %s', $client_IP{$client});
			return(1);
		}
	}
	# process status requests
	elsif ($msg_ref->{'identifier'} eq 'status')
	{
		# stream-specific status
		if (exists($msg_ref->{'stream'}))
		{
			sendStreamStatus($client, $msg_ref->{'stream'});
			return(1);
		}
		# general status
		else
		{
			sendGeneralStatus($client);
			return(1);
		}
	}

	# all messages beyond here require a 'stream' key, so test that we have one
	if (! exists($msg_ref->{'stream'}))
	{
		sendMessage($client,
		            makeMessage(
		               'identifier' => 'fail',
		               'command'    => $msg_ref->{'identifier'},
		               'error'      => sprintf('Requests of type %s require a stream to be specified',
		                                       $msg_ref->{'identifier'}),
		                       ),
				   );
		printLog('Client %d requested operation "%s", but supplied no stream name',
			$client_ID{$client}, $msg_ref->{'identifier'});
		return(1);
	}

	# standardize case of stream ID
	$msg_ref->{'stream'} = uc($msg_ref->{'stream'});

	# make sure that the given stream exists
	if (! streamExists($msg_ref->{'stream'}))
	{
		sendMessage($client,
		            makeMessage(
		               'identifier' => 'fail',
		               'command'	 => $msg_ref->{'identifier'},
		               'error'		 => sprintf('Stream %s does not exist',
		                                        $msg_ref->{'stream'})
		                       )
		           );
		printLog('Client %d requested operation "%s" on stream %s, but stream does not exist',
					$client_ID{$client}, $msg_ref->{'identifier'}, $msg_ref->{'stream'});
		return(1);
	}
	# message structure looks good; start processing tokens
	else
	{
		switch ($msg_ref->{'identifier'})
		{
			case 'open'
			{
				addClientToStream($client, $msg_ref->{'stream'}, $msg_ref->{'mode'});
				return(1);
			}
			case 'close'
			{
				removeClientFromStream($client, $msg_ref->{'stream'});
				return(1);
			}
			case 'write'
			{
				if (! exists($msg_ref->{'data'}))
				{
					sendMessage($client,
									makeMessage('identifier' => 'fail',
														 'error'		  => 'Missing data element',
														  'command'		=> 'write')
									);
					printLog('Client %d requested a write to stream %s, but no data was supplied',
								$client_ID{$client},
								$msg_ref->{'stream'});
					return(0);
				}
				writeToStream($client, $msg_ref->{'stream'}, $msg_ref->{'data'});
				return(1);
			}
			else
			{
				printLog('Unknown identifer "%s" in message from %s',
							$msg_ref->{'identifier'}, $client_IP{$client});
				reportErrorToClient($client, 'Unknown identifier: %s', $msg_ref->{'identifier'});
				return(0);
			}
		}
	}
	return(0);
}

## @cmethod void pingClients()
# Pings all currently-connected clients.
sub pingClients()
{
	my $client;

	foreach $client (keys(%client_IP))
	{
		sendPingRequest($client);
	}
}

## @cmethod boolean clientIsAlive($client)
# Tests whether or not the given client is alive.
# Uses IO::Socket::connected() to see if client is still connected, and
# then checks to see if client has timed out on a ping.
# If the client has timed out on a ping, it's removed.
#
# @param client Client connection handle
sub clientIsAlive($)
{
	my $client = shift;

	# check that the handle is defined and we have a socket-level
	# connection
	return(0) unless ($client && $client->opened() && $client->connected());

	# check that the client has responded to a ping recently
	if ( exists($last_heard_from{$client}) &&
		((time - $last_heard_from{$client}) < CLIENT_PING_TIMEOUT))
	{
		return(1);
	}

	printLog('Client %d (%s) has not responded to a ping in %d seconds -- hanging up its connection',
				$client_ID{$client}, $client_IP{$client}, time - $last_heard_from{$client});

	removeClient($client);

	return(0);
}

## @cmethod void reportErrorToClient($client, ...)
# Sends an error message to a client.
# The message is everything after the first parameter.  It is treated as a
# sprintf()-style string.
#
# @param client The client handle to which to send the message
sub reportErrorToClient($;@)
{
	my $client = shift;

	# nothing to do if we have nothing to say
	return unless ($#_ >= 0);

	sendMessage($client, makeMessage('identifier' => 'fail',
												'error'		 => sprintf(@_)));
}

## @cmethod void sendPingRequest($client)
# Sends a ping-request message to the indicated client.
#
# @param client The handle of the client to which the ping-request
#	 should be sent
sub sendPingRequest($)
{
	my $client = shift;
	my $msg_ref;
	my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime();

	$msg_ref = makeMessage('identifier' => 'ping-request');

	$msg_ref->{'time'} = sprintf("%04d%02d%02d %02d:%02d:%02d",
	$year + 1900,
	$mon + 1,
	$mday,
	$hour,
	$min,
	$sec);

	sendMessage($client, $msg_ref);
}

## @cmethod void sendPingResponse($client)
# Sends a ping-response message to the indicated client.
#
# @param client The client handle
sub sendPingResponse($)
{
	my $client = shift;

	sendMessage($client, makeMessage('identifier' => 'ping-response'));
}

## @cmethod void sendStreamStatus($client, $stream)
# Sends a stream-specific status update to the indicated client for
# the indicated stream.
#
# @param client Client handle
# @param stream Name of stream in question
sub sendStreamStatus($$)
{
	my $client = shift;
	my $stream = shift;
	my $msg_ref;

	printDbg('Responding to request for status for stream %s from client %d',
				$stream, $client_ID{$client});

	$msg_ref = makeMessage('identifier' => 'ok',
								  'command' => 'status',
								  'stream' => $stream,
								  'listeners' => 0,
								  'writer' => 0
								 );
	$msg_ref->{'listeners'} = $#{$stream_listeners{$stream}} + 1;
	if (exists($stream_writer{$stream}))
	{
		$msg_ref->{'writer'} = $client_IP{$stream_writer{$stream}};
	}

	sendMessage($client, $msg_ref);
}

## @cmethod void sendGeneralStatus($client)
# Sends a general status message to the given client handle.
#
# @param client client handle
sub sendGeneralStatus($)
{
	my $client = shift;
	my $uptime = time - $start_time;
	my $days = int($uptime / 86400);
	my $hours = ($uptime % 86400) / 3600;
	my $minutes = (($uptime % 86400) % 3600) / 60;
	my $msg_ref;

	printDbg('Responding to general status request from client %d',
				$client_ID{$client});

	$msg_ref = makeMessage('identifier' => 'ok',
								  'command' => 'status'
								 );

	@{$msg_ref->{'streams'}} = keys(%stream_devices);
	$msg_ref->{'client_count'} = keys(%client_IP);
	$msg_ref->{'uptime'} = sprintf('%02d days %02d hours %02d minutes',
											 $days, $hours, $minutes);
	$msg_ref->{'server-id'} = $ID;

	sendMessage($client, $msg_ref);
}

## @cmethod void addClientToStream($client, $stream, $mode)
# Adds a client to a stream using the indicated permissions.
#
# If no mode string is given, stream is opened in read mode.
# If read-write permission is requested but not available, read
# permission will be granted and a warning will be included
# indicating that write permission wasn't granted.
# If write permission is requested but not available, an
# error will be generated.
sub addClientToStream($$;$)
{
	my $client = shift;
	my $stream = shift;
	my $mode = shift;
	my $response;
	my @modes;

	if (! defined($mode))
	{
		$mode = 'read';
		printLog('Client %d requested open on stream %s without mode string; defaulting to read-only',
					$client_ID{$client}, $stream);
	}

	# split up the mode string into a list of modes
	@modes = split(/[-_ \/\\]+/, $mode);

	$response = makeMessage('identifier' => 'ok',
									'command' => 'open',
									'stream' => $stream,
									'mode' => "");

	# if no open mode was given, or read was specifically requested, add client to
	# list of listeners on stream
	if (grep { /read/i } @modes)
	{
		# only add the client to the list of listeners if they're not already in there,
		# but still return 'ok'
		if (! grep {$_ == $client} @{$stream_listeners{$stream}})
		{
			push(@{$stream_listeners{$stream}}, $client);

			printLog("Adding client %d to stream %s (now %d listeners)",
						$client_ID{$client},
						$stream,
						$#{$stream_listeners{$stream}} + 1);
		}
		else
		{
			push(@{$response->{'warnings'}}, "Read access already granted");
		}

		$response->{'mode'} .= "read ";
	}

	# If the client has requested write access, only grant it if nobody else already has
	# it or if the client which had previously asserted access has disappeared.
	# If the client HASN'T requested write access on this open and they've already got
	# the stream open with write access, revoke write access for the client
	if (grep { /write/i } @modes)
	{
		if (exists($stream_writer{$stream}))
		{
			if (clientIsAlive($stream_writer{$stream}))
			{
				$response->{'identifier'} = 'fail';
				$response->{'error'} = sprintf('Write access not available; client %d (%s) holds talking stick',
													$client_ID{$stream_writer{$stream}},
													$client_IP{$client_ID{$stream_writer{$stream}}});
				printLog('Rejecting request for write access to stream %s for client %d',
					$stream, $client_ID{$client});
			}
			elsif ($stream_writer{$stream} == $client)
			{
				printLog('Client %d requested write access for stream %s when it already had write access',
							$client_ID{$client}, $stream);
				push(@{$response->{'warnings'}}, "Write access already granted to you");
				$response->{'mode'} .= "write";
			}
			else
			{
				printLog('Setting client %d as writer for stream %s', $client_ID{$client}, $stream);
				$stream_writer{$stream} = $client;
				$response->{'mode'} .= "write";
			}
		}
		else
		{
			printLog('Setting client %d as writer for stream %s', $client_ID{$client}, $stream);
			$stream_writer{$stream} = $client;
			$response->{'mode'} .= "write";
		}
	}
	elsif (exists($stream_writer{$stream}) && ($stream_writer{$stream} == $client))
	{
		# if the client previously had write permission on this stream but is now
		# opening it w/o write permission, remove the write permission it previously
		# held
		printLog('Removing client %d as writer for stream %s', $client_ID{$client}, $stream);
		delete($stream_writer{$stream});
	}

	sendMessage($client, $response) if defined($client);
}

sub removeClientFromStream($$)
{
	my $client = shift;
	my $stream = shift;
	my $response;
	my $client_idx;

	$response = makeMessage('identifier' => 'ok',
							'command'    => 'close',
							'stream'     => $stream);

	for ($client_idx = 0; $client_idx <= $#{$stream_listeners{$stream}}; $client_idx++)
	{
		last if ($stream_listeners{$stream}->[$client_idx] == $client);
	}
	# we found it -- remove it
	if ($client_idx <= $#{$stream_listeners{$stream}})
	{
		printLog("Removing client %d from stream %s (now %d listeners)",
					$client_ID{$client},
					$stream,
					$#{$stream_listeners{$stream}});

		splice(@{$stream_listeners{$stream}}, $client_idx, 1);
	}
	else
	{
		push(@{$response->{'warnings'}}, "You are not subscribed to stream $stream");
	}

	# only send the message if we haven't closed the connection with it
	sendMessage($client, $response) if (defined($client) && exists($client_IP{$client}));
}

## @cmethod string getSysname()
# Returns the name of this system.
sub getSysname()
{
	return hostname();
}

## @cmethod void usage()
# Prints out a usage statement culled from the POD document at the end of this file.
sub usage(;$)
{
	pod2usage($_[0]) if (defined($_[0]));
	pod2usage(0);
}

## @cmethod void printLog(@args)
# Logs the given message to the server's log file.
# Arguments can be a single string or a sprintf-style list of arguments.
#
# @param args A sprintf-style string to print to the logfile
sub printLog(@)
{
	syslog(LOG_INFO, @_);
}

## @cmethod void printDbg(@args)
# Prints the given message as a debug message.
#
# @param args A sprintf-stype string to print to our debug output
sub printDbg(@)
{
	syslog(LOG_DEBUG, @_);
}

## @cmethod void printWarn(@args)
# Logs the given sprintf()-style string as an error message.
# <WARNING> tags are added to surround the given message.
#
# @param args sprintf()-style argument(s)
sub printWarn(@)
{
	my $format_str = shift;
	
	chomp($format_str);
	$format_str = "<WARNING>$format_str</WARNING>";
	syslog(LOG_ERR, $format_str, @_);
}

## @cmethod void printErr(@args)
# Logs the given sprintf()-style string as an error message.
# <ERROR> tags are added to surround the given message.
#
# @param args sprintf()-style argument(s)
sub printErr(@)
{
	my $format_str = shift;
	
	chomp($format_str);
	$format_str = "<ERROR>$format_str</ERROR>";
	syslog(LOG_ERR, $format_str, @_);
}

## @cmethod void termErr($error_string)
# Logs the given terminal error condition and shuts us down.
#
# @param error_string The error condition responsible for the shutdown
sub termErr(@)
{
	my @carplines;
	my $line;

	# log what Carp::confess will print to STDERR so that we can see
	# the stack backtrace in the logs
	$line = sprintf(shift(@_), @_);
	@carplines = split(/\n/, Carp::longmess($line));
	foreach $line (@carplines)
	{
		printErr($line);
	}

	Carp::confess($line);
}

## signal handler for SIGHUP
sub handle_sighup($)
{
	syslog(LOG_INFO, "Caught SIGHUP");
	$re_starting = 1;
}

## signal handler for deadly signals
sub handle_deathsig($)
{
	# signal number passed to us
	my $caught_sig = shift;

	syslog(LOG_NOTICE, 'Caught SIG%s', $caught_sig);
	$shutting_down = 1;
}

## signal handler for child processes which finished
sub handle_kid($)
{
	my $caught_sig = shift;
	my $kidpid;

	$kidpid = wait;

	return unless ($kidpid == $hup_scheduled);

	$hup_scheduled = 0;

	printDbg("HUP process complete.");
}



__END__

=head1 NAME

consoled - debug console stream management daemon

=head1 SYNOPSIS

consoled <options> [PCFG file]

For more information, please type C<perldoc consoled>

=head1 DESCRIPTION

Provides a networked interface to debug output monitors.

Allows any number of clients to share read access to local serial devices, while
allowing only one such client to write to each device at any one time.

=head1 OPTIONS

Below is a list of options able to be given to consoled.
Note that non-option parameters override option parameters.

=over 3

=item --pcfg [PCFG file]

Supply the name of the PCFG file to be used.  Must be given with
the absolute path to the file.

=item --pcfg-dir [PCFG dir]

Supply the directory which is to be used as the base directory for resolving
the names of PCFG files included from within other PCFG files.  Since
the INCLUDE_PCFG directive supplies a relative path, we need a starting point
from which to resolve that relative path.   This option allows us to be given
that starting point.

=item --dummy

If given, causes a stream called DUMMY to be created, whose output will be
the current time, once per second in date(1) format, and which will not react
to input, should one write to the stream.

The primary use of this switch is to create a stream which is guaranteed to
have particular data on it.

=item --fake-it

If given, causes consoled to ignore any PCFG settings and to provide only
the DUMMY device.

The primary use of this switch is for off-line testing of consoled.

=back

=head1 AUTHOR

Catherine Mitchell

=cut
