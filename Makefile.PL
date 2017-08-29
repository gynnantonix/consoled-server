use inc::Module::Install;
use Cwd;
use File::Spec;

my $version;


## if the file VERSION exists, it contains our version; otherwise,
## we use the version encoded in the containing directory name as our version,
## and create the VERSION file.
if ( -r 'VERSION' )
{
	open(VERS, 'VERSION');
	do {
		$version = <VERS>;
	} while ($version !~ /[\w\d]+/);
	close(VERS);
	chomp($version);
	print("Version $version\n");
}
else
{
	my @dirs;
	my $version_from_dir;
	my $vers;
	
	# pull the current working directory into a list of parent directories
	@dirs = File::Spec->splitdir(getcwd());
	# our containing directory will be named by our release number
	$version_from_dir = pop(@dirs);
	# make sure that the previous comment is true
	if (! (defined($version_from_dir) && ($version_from_dir =~ /^\d+/)))
	{
		$version_from_dir = 'DEVELOPMENT';
	}
	elsif ($version_from_dir =~ /^\d{8}/)
	{
		$version_from_dir = "RC_$version_from_dir";
	}
	
	$version = $version_from_dir;
	
	# create version line
	$vers = 'my $VERSION = \'' . $version_from_dir . "';\n";
	
	open(VERS, '>VERSION') or die("Unable to create VERSION file: $!");
	print(VERS "$version_from_dir\n");
	close(VERS);
	
	## set the $VERSION variable in each file to whatever we figured
	## out above.  Since our files are named *.pl before packaging, we'll
	## write the modified version to the base filename without the .pl
	
	my $file;
	
	foreach $file ('sbin/consoled.pl')
	{
		my $newfilename;
		my @newfile;
		my $line;
		
		# don't re-name our library modules
		if ($file =~ /\.pm$/)
		{
			$newfilename = $file;
		}
		else
		{
			($newfilename) = ($file =~ /(.*)\.pl$/);
		}
		
		open(ORIG, $file) or die("Unable to read $file: $!");
		
		# remove all '$VERSION =' lines and replace them with this version
		foreach $line (<ORIG>)
		{
			if ($line =~ /\s*\$VERSION\s*=/)
			{
				push(@newfile, $vers);
			}
			else
			{
				push(@newfile, $line);
			}
		}
		close(ORIG);
		
		# write consoled
		open(TAGGED, ">$newfilename") or die("Can't write tagged $newfilename: $!");
		foreach $line (@newfile)
		{
			print(TAGGED $line);
		}
		close(TAGGED);
		
		chmod(0755, $newfilename);
	}
}



# Define metadata
name           'consoled';
abstract       "Perl-based implementation of consoled console server";
author         "Catherine Mitchell";
perl_version   '5.14';
license        'perl';
version        $version;


# say what we need
configure_requires   'File::Copy'       => 0;
configure_requires   'Sys::Syslog'      => 0.27;
configure_requires   'Unix::PID'        => 0;
configure_requires   'Proc::Daemon'     => 0;
configure_requires   'Device::SerialPort' => 0;
configure_requires   'Net::Telnet'      => 0;
configure_requires   'JSON'             => 0;

# say what doesn't need to be indexed
no_index       'directory'        => 'docs';

# copy renamed scripts to install locations
install_script  'sbin/consoled';

WriteAll;
