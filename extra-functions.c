/*
 * Copyright (C) 2011 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <paths.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include <ctype.h>
#include "cutils/misc.h"
#include "cutils/properties.h"
#include <dirent.h>
#include <getopt.h>
#include <linux/input.h>
#include <signal.h>
#include <sys/limits.h>
#include <termios.h>
#include <time.h>
#include <sys/vfs.h>

#include "tw_reboot.h"
#include "bootloader.h"
#include "common.h"
#include "extra-functions.h"
#include "cutils/properties.h"
#include "install.h"
#include "minuitwrp/minui.h"
#include "minzip/DirUtil.h"
#include "minzip/Zip.h"
#include "recovery_ui.h"
#include "roots.h"
#include "ddftw.h"
#include "backstore.h"
#include "themes.h"
#include "data.h"
#include "format.h"

//kang system() from bionic/libc/unistd and rename it __system() so we can be even more hackish :)
#undef _PATH_BSHELL
#define _PATH_BSHELL "/sbin/sh"

static const char *SIDELOAD_TEMP_DIR = "/tmp/sideload";
extern char **environ;

// sdcard partitioning variables
char swapsize[32];
int swap;
char extsize[32];
int ext;
int ext_format; // 3 or 4

int
__system(const char *command)
{
  pid_t pid;
	sig_t intsave, quitsave;
	sigset_t mask, omask;
	int pstat;
	char *argp[] = {"sh", "-c", NULL, NULL};

	if (!command)		/* just checking... */
		return(1);

	argp[2] = (char *)command;

	sigemptyset(&mask);
	sigaddset(&mask, SIGCHLD);
	sigprocmask(SIG_BLOCK, &mask, &omask);
	switch (pid = vfork()) {
	case -1:			/* error */
		sigprocmask(SIG_SETMASK, &omask, NULL);
		return(-1);
	case 0:				/* child */
		sigprocmask(SIG_SETMASK, &omask, NULL);
		execve(_PATH_BSHELL, argp, environ);
    _exit(127);
  }

	intsave = (sig_t)  bsd_signal(SIGINT, SIG_IGN);
	quitsave = (sig_t) bsd_signal(SIGQUIT, SIG_IGN);
	pid = waitpid(pid, (int *)&pstat, 0);
	sigprocmask(SIG_SETMASK, &omask, NULL);
	(void)bsd_signal(SIGINT, intsave);
	(void)bsd_signal(SIGQUIT, quitsave);
	return (pid == -1 ? -1 : pstat);
}

static struct pid {
	struct pid *next;
	FILE *fp;
	pid_t pid;
} *pidlist;

FILE *
__popen(const char *program, const char *type)
{
	struct pid * volatile cur;
	FILE *iop;
	int pdes[2];
	pid_t pid;

	if ((*type != 'r' && *type != 'w') || type[1] != '\0') {
		errno = EINVAL;
		return (NULL);
	}

	if ((cur = malloc(sizeof(struct pid))) == NULL)
		return (NULL);

	if (pipe(pdes) < 0) {
		free(cur);
		return (NULL);
	}

	switch (pid = vfork()) {
	case -1:			/* Error. */
		(void)close(pdes[0]);
		(void)close(pdes[1]);
		free(cur);
		return (NULL);
		/* NOTREACHED */
	case 0:				/* Child. */
	    {
		struct pid *pcur;
		/*
		 * because vfork() instead of fork(), must leak FILE *,
		 * but luckily we are terminally headed for an execl()
		 */
		for (pcur = pidlist; pcur; pcur = pcur->next)
			close(fileno(pcur->fp));

		if (*type == 'r') {
			int tpdes1 = pdes[1];

			(void) close(pdes[0]);
			/*
			 * We must NOT modify pdes, due to the
			 * semantics of vfork.
			 */
			if (tpdes1 != STDOUT_FILENO) {
				(void)dup2(tpdes1, STDOUT_FILENO);
				(void)close(tpdes1);
				tpdes1 = STDOUT_FILENO;
			}
		} else {
			(void)close(pdes[1]);
			if (pdes[0] != STDIN_FILENO) {
				(void)dup2(pdes[0], STDIN_FILENO);
				(void)close(pdes[0]);
			}
		}
		execl(_PATH_BSHELL, "sh", "-c", program, (char *)NULL);
		_exit(127);
		/* NOTREACHED */
	    }
	}

	/* Parent; assume fdopen can't fail. */
	if (*type == 'r') {
		iop = fdopen(pdes[0], type);
		(void)close(pdes[1]);
	} else {
		iop = fdopen(pdes[1], type);
		(void)close(pdes[0]);
	}

	/* Link into list of file descriptors. */
	cur->fp = iop;
	cur->pid =  pid;
	cur->next = pidlist;
	pidlist = cur;

	return (iop);
}

/*
 * pclose --
 *	Pclose returns -1 if stream is not associated with a `popened' command,
 *	if already `pclosed', or waitpid returns an error.
 */
int
__pclose(FILE *iop)
{
	struct pid *cur, *last;
	int pstat;
	pid_t pid;

	/* Find the appropriate file pointer. */
	for (last = NULL, cur = pidlist; cur; last = cur, cur = cur->next)
		if (cur->fp == iop)
			break;

	if (cur == NULL)
		return (-1);

	(void)fclose(iop);

	do {
		pid = waitpid(cur->pid, &pstat, 0);
	} while (pid == -1 && errno == EINTR);

	/* Remove the entry from the linked list. */
	if (last == NULL)
		pidlist = cur->next;
	else
		last->next = cur->next;
	free(cur);

	return (pid == -1 ? -1 : pstat);
}

char* sanitize_device_id(char* id)
{
        const char* whitelist ="abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890-._";
        char* c = id;
        char* str = (int*) calloc(50, sizeof *id);
        while (*c)
        {
                if (strchr(whitelist, *c))
                {
                        strncat(str, c, 1);
                }
                c++;
        }
        return str;
}

#define CMDLINE_SERIALNO        "androidboot.serialno="
#define CMDLINE_SERIALNO_LEN    (strlen(CMDLINE_SERIALNO))
#define CPUINFO_SERIALNO        "Serial"
#define CPUINFO_SERIALNO_LEN    (strlen(CPUINFO_SERIALNO))
#define CPUINFO_HARDWARE        "Hardware"
#define CPUINFO_HARDWARE_LEN    (strlen(CPUINFO_HARDWARE))

void get_device_id()
{
	FILE *fp;
	char line[2048];
	char hardware_id[32];
	char* token;
	char* new_device_id;

    // Assign a blank device_id to start with
    device_id[0] = 0;
#ifndef TW_FORCE_CPUINFO_FOR_DEVICE_ID
    // First, try the cmdline to see if the serial number was supplied
	fp = fopen("/proc/cmdline", "rt");
	if (fp != NULL)
    {
        // First step, read the line. For cmdline, it's one long line
        fgets(line, sizeof(line), fp);
        fclose(fp);

        // Now, let's tokenize the string
        token = strtok(line, " ");

        // Let's walk through the line, looking for the CMDLINE_SERIALNO token
        while (token)
        {
            // We don't need to verify the length of token, because if it's too short, it will mismatch CMDLINE_SERIALNO at the NULL
            if (memcmp(token, CMDLINE_SERIALNO, CMDLINE_SERIALNO_LEN) == 0)
            {
                // We found the serial number!
                strcpy(device_id, token + CMDLINE_SERIALNO_LEN);
		new_device_id = sanitize_device_id(device_id);
		strcpy(device_id, new_device_id);
		free(new_device_id);
                return;
            }
            token = strtok(NULL, " ");
        }
    }
#endif
	// Now we'll try cpuinfo for a serial number
	fp = fopen("/proc/cpuinfo", "rt");
	if (fp != NULL)
    {
		while (fgets(line, sizeof(line), fp) != NULL) { // First step, read the line.
			if (memcmp(line, CPUINFO_SERIALNO, CPUINFO_SERIALNO_LEN) == 0)  // check the beginning of the line for "Serial"
			{
				// We found the serial number!
				token = line + CPUINFO_SERIALNO_LEN; // skip past "Serial"
				while ((*token > 0 && *token <= 32 ) || *token == ':') token++; // skip over all spaces and the colon
				if (*token != 0) {
                    token[30] = 0;
					if (token[strlen(token)-1] == 10) { // checking for endline chars and dropping them from the end of the string if needed
						memset(device_id, 0, sizeof(device_id));
						strncpy(device_id, token, strlen(token) - 1);
					} else {
						strcpy(device_id, token);
					}
					LOGI("=> serial from cpuinfo: '%s'\n", device_id);
					fclose(fp);
					new_device_id = sanitize_device_id(device_id);
					strcpy(device_id, new_device_id);
					free(new_device_id);
					return;
				}
			} else if (memcmp(line, CPUINFO_HARDWARE, CPUINFO_HARDWARE_LEN) == 0) {// We're also going to look for the hardware line in cpuinfo and save it for later in case we don't find the device ID
				// We found the hardware ID
				token = line + CPUINFO_HARDWARE_LEN; // skip past "Hardware"
				while ((*token > 0 && *token <= 32 ) || *token == ':')  token++; // skip over all spaces and the colon
				if (*token != 0) {
                    token[30] = 0;
					if (token[strlen(token)-1] == 10) { // checking for endline chars and dropping them from the end of the string if needed
                        memset(hardware_id, 0, sizeof(hardware_id));
						strncpy(hardware_id, token, strlen(token) - 1);
					} else {
						strcpy(hardware_id, token);
					}
					LOGI("=> hardware id from cpuinfo: '%s'\n", hardware_id);
				}
			}
		}
		fclose(fp);
    }
	
	if (hardware_id[0] != 0) {
		LOGW("\nusing hardware id for device id: '%s'\n", hardware_id);
		strcpy(device_id, hardware_id);
		new_device_id = sanitize_device_id(device_id);
		strcpy(device_id, new_device_id);
		free(new_device_id);
		return;
	}

    strcpy(device_id, "serialno");
	LOGE("=> device id not found, using '%s'.", device_id);
    return;
}

char* get_path (char* path)
{
        char *s;

        /* Go to the end of the string.  */
        s = path + strlen(path) - 1;

        /* Strip off trailing /s (unless it is also the leading /).  */
        while (path < s && s[0] == '/')
                s--;

        /* Strip the last component.  */
        while (path <= s && s[0] != '/')
                s--;

        while (path < s && s[0] == '/')
                s--;

        if (s < path)
                return ".";

        s[1] = '\0';
	return path;
}

char* basename(char* name) 
{
	const char* base;	
	for (base = name; *name; name++)
	{
		if(*name == '/')
		{
			base = name + 1;
		}		
	}
	return (char *) base;
}
/*
    Checks md5 for a path
    Return values:
        -1 : MD5 does not exist
        0 : Failed
        1 : Success
*/
int check_md5(char* path) {
    int o; 
    char cmd[PATH_MAX + 30];
    char md5file[PATH_MAX + 40];
    strcpy(md5file, path);
    strcat(md5file, ".md5");
    char dirpath[PATH_MAX];
    char* file;
    if (access(md5file, F_OK ) != -1) {
	strcpy(dirpath, md5file);
	get_path(dirpath);
	chdir(dirpath);
	file = basename(md5file);
	sprintf(cmd, "/sbin/busybox md5sum -c '%s'", file);
	FILE * cs = __popen(cmd, "r");
	char cs_s[PATH_MAX + 50];
	fgets(cs_s, PATH_MAX + 50, cs);
	char* OK = strstr(cs_s, "OK");
	if (OK != NULL) {
		printf("MD5 is good. returning 1\n");
		o = 1;
	}
	else {
		printf("MD5 is bad. return -2\n");
		o = -2;
	}

	__pclose(cs);
    } 
    else {
	//No md5 file
	printf("setting o to -1\n");
	o = -1;
    }

    return o;
}

static void set_sdcard_update_bootloader_message() {
    struct bootloader_message boot;
    memset(&boot, 0, sizeof(boot));
    strlcpy(boot.command, "boot-recovery", sizeof(boot.command));
    strlcpy(boot.recovery, "recovery\n", sizeof(boot.recovery));
    set_bootloader_message(&boot);
}


 
void fix_perms()
{
	ensure_path_mounted("/data");
	ensure_path_mounted("/system");
	ui_show_progress(1,30);
    ui_print("\n-- Fixing Permissions\n");
	ui_print("This may take a few minutes.\n");
	__system("./sbin/fix_permissions.sh");
	ui_print("-- Done.\n\n");
	ui_reset_progress();
}

void fix_loop()
{ 
 //   run_program("/sbin/erase_image", "misc");
//	run_program("/sbin/erase_image", "persist");
	__system("rm -r /dev/mtd/mtd8");
	__system("erase_image misc");
	__system("/sbin/erase_image misc");
	__system("erase_image persist");
	__system("/sbin/erase_image persist");
//	flash_eraseall /dev/mtd/mtd8
//	erase_image("misc");
//	erase_image("persist");
 //   format_root_device("PERSIST:");
//    __reboot(LINUX_REBOOT_MAGIC1, LINUX_REBOOT_MAGIC2, LINUX_REBOOT_CMD_RESTART2, "");
//	ui_show_progress(1,30);				
    ui_print("\n-- Fixing recovery bootloop\n");
//	reboot(RB_AUTOBOOT);
	__system("./sbin/rebootrecovery.sh");
//	tw_reboot(rb_recovery);
//     __reboot(LINUX_REBOOT_MAGIC1, LINUX_REBOOT_MAGIC2, LINUX_REBOOT_CMD_RESTART2, (void*) "recovery");	
//    reboot_recovery(); 
} 


void advanced_menu()
{
	// ADVANCED MENU
	#define ITEM_REBOOT_MENU       0
	#define ITEM_FORMAT_MENU       1
	#define ITEM_MISC              2 
	#define ITEM_FIX_PERM          3
	#define ITEM_ALL_SETTINGS      4
	#define ITEM_SDCARD_PART       5
	#define ITEM_CPY_LOG		   6
	#define ADVANCED_MENU_BACK     7
    
	char* MENU_ADVANCED[] = { "Reboot Menu",
	                          "Format Menu",
							  "Fix Recovery Boot Loop",
	                          "Fix Permissions",
	                          "Change twrp Settings",
							  "Partition SD Card",
	                          "Copy recovery log to /sdcard",
	                          "<-- Back To Main Menu",
	                          NULL };
	
	const char* MENU_ADVANCED_HEADERS[] = { "Advanced Menu",
    										"Reboot, Format, or twrp!",
                                             NULL };

    char** headers = prepend_title(MENU_ADVANCED_HEADERS);
    
    inc_menu_loc(ADVANCED_MENU_BACK);
    for (;;)
    {
        int chosen_item = get_menu_selection(headers, MENU_ADVANCED, 0, 0);
        switch (chosen_item)
        {
            case ITEM_REBOOT_MENU:
                reboot_menu();
                break;
            case ITEM_FORMAT_MENU:
                format_menu();
                break;
			case ITEM_MISC:
                fix_loop();
                break;                 
            case ITEM_FIX_PERM:
            	fix_perms();
                break;
            case ITEM_ALL_SETTINGS:
			    all_settings_menu(0);
				break;
			case ITEM_SDCARD_PART:
				show_menu_partition();
				break;
            case ITEM_CPY_LOG:
                mount_current_storage();
				char mount_point[255], command[255];
				strcpy(mount_point, DataManager_GetSettingsStorageMount());
				sprintf(command, "cp /tmp/recovery.log %s", mount_point);
				__system(command);
				sync();
                ui_print("Copied recovery log to storage.\n");
            	break;
            case ADVANCED_MENU_BACK:
            	dec_menu_loc();
            	return;
        }
	    if (go_home) { 
	        dec_menu_loc();
	        return;
	    }
    }
}

// kang'd this from recovery.c cuz there wasnt a recovery.h!
int erase_volume(const char *volume) {
    ui_print("Formatting %s...\n", volume);

    if (strcmp(volume, "/cache") == 0) {
        // Any part of the log we'd copied to cache is now gone.
        // Reset the pointer so we copy from the beginning of the temp
        // log.
        tmplog_offset = 0;
    }

    return format_volume(volume);
}

// FORMAT MENU
void format_menu()
{
	struct stat st;
	
	#define ITEM_FORMAT_SYSTEM      0
	#define ITEM_FORMAT_DATA        1
	#define ITEM_FORMAT_CACHE       2
	#define ITEM_FORMAT_SDCARD      3
	#define ITEM_FORMAT_SDEXT		4
	#define ITEM_FORMAT_BACK        5
	
	const char* part_headers[] = {    "Format Menu",
                                "Choose a Partition to Format: ",
                                NULL };
	
    char* part_items[] = { 	"Format SYSTEM (/system)",
                            "Format DATA (/data)",
            				"Format CACHE (/cache)",
                            "Format SDCARD (/sdcard)",
                            "Format SD-EXT (/sd-ext)",
						    "<-- Back To Advanced Menu",
						    NULL };

    char** headers = prepend_title(part_headers);
    
    inc_menu_loc(ITEM_FORMAT_BACK);
	for (;;)
	{
//                ui_set_background(BACKGROUND_ICON_WIPE_CHOOSE);
		int chosen_item = get_menu_selection(headers, part_items, 0, 0);
		switch (chosen_item)
		{
			case ITEM_FORMAT_SYSTEM:
				confirm_format("SYSTEM", "/system");
				break;
			case ITEM_FORMAT_DATA:
                confirm_format("DATA", "/data");
                break;
			case ITEM_FORMAT_CACHE:
                confirm_format("CACHE", "/cache");
                break;
			case ITEM_FORMAT_SDCARD:
                confirm_format("SDCARD", "/sdcard");
                break;
            case ITEM_FORMAT_SDEXT:
            	if (stat(sde.blk,&st) == 0)
            	{
                	__system("mount /sd-ext");
                    confirm_format("SD-EXT", "/sd-ext");
            	} else {
            		ui_print("\n/sd-ext not detected! Aborting.\n");
            	}
            	break;
			case ITEM_FORMAT_BACK:
            	dec_menu_loc();
 //               ui_set_background(BACKGROUND_ICON_MAIN);
				return;
		}
	    if (go_home) { 
    	        dec_menu_loc();
   //             ui_set_background(BACKGROUND_ICON_MAIN);
	        return;
	    }
	}
}

void
confirm_format(char* volume_name, char* volume_path) {

    char* confirm_headers[] = { "Confirm Format of Partition: ",
                        volume_name,
                        "",
                        "  THIS CAN NOT BE UNDONE!",
                        NULL };

    char* items[] = {   "No",
                        "Yes -- Permanently Format",
                        NULL };
    
    char** headers = prepend_title((const char**)confirm_headers);
    
    inc_menu_loc(0);
    int chosen_item = get_menu_selection(headers, items, 1, 0);
    if (chosen_item != 1) {
        dec_menu_loc();
        return;
    } else {
   //     ui_set_background(BACKGROUND_ICON_WIPE);
        ui_print("\n-- Wiping %s Partition...\n", volume_name);
        erase_volume(volume_path);
        ui_print("-- %s Partition Wipe Complete!\n", volume_name);
        dec_menu_loc();
    }
}




void inc_menu_loc(int bInt)
{
	menu_loc_idx++;
	menu_loc[menu_loc_idx] = bInt;
	//ui_print("=> Increased Menu Level; %d : %d\n",menu_loc_idx,menu_loc[menu_loc_idx]);  //TURN THIS ON TO DEBUG
}
void dec_menu_loc()
{
	menu_loc_idx--;
	//ui_print("=> Decreased Menu Level; %d : %d\n",menu_loc_idx,menu_loc[menu_loc_idx]); //TURN THIS ON TO DEBUG
}

#define MNT_SYSTEM 	0
#define MNT_DATA	1
#define MNT_CACHE	2
#define MNT_SDCARD	3
#define MNT_SDEXT	4
#define MNT_BACK	5

void chkMounts()
{
	FILE *fp;
	char tmpOutput[255];
	sysIsMounted = 0;
	datIsMounted = 0;
	cacIsMounted = 0;
	sdcIsMounted = 0;
	sdeIsMounted = 0;
	fp = __popen("cat /proc/mounts", "r");
	while (fgets(tmpOutput,255,fp) != NULL)
	{
	    sscanf(tmpOutput,"%s %*s %*s %*s %*d %*d",tmp.blk);
	    if (strcmp(tmp.blk,sys.blk) == 0)
	    {
	    	sysIsMounted = 1;
	    }
	    if (strcmp(tmp.blk,dat.blk) == 0)
	    {
	    	datIsMounted = 1;
	    }
	    if (strcmp(tmp.blk,cac.blk) == 0)
	    {
	    	cacIsMounted = 1;
	    }
	    if (strcmp(tmp.blk,sdcext.blk) == 0)
	    {
	    	sdcIsMounted = 1;
	    }
	    if (strcmp(tmp.blk,sde.blk) == 0)
	    {
	    	sdeIsMounted = 1;
	    }
	}
	__pclose(fp);
}

char* isMounted(int mInt)
{
	int isTrue = 0;
	struct stat st;
	char* tmp_set = (char*)malloc(25);
	if (mInt == MNT_SYSTEM)
	{
	    if (sysIsMounted == 1) {
			strcpy(tmp_set, "unmount");
	    } else {
			strcpy(tmp_set, "mount");
	    }
		strcat(tmp_set, " /system");
	}
	if (mInt == MNT_DATA)
	{
	    if (datIsMounted == 1) {
			strcpy(tmp_set, "unmount");
	    } else {
			strcpy(tmp_set, "mount");
	    }
		strcat(tmp_set, " /data");
	}
	if (mInt == MNT_CACHE)
	{
	    if (cacIsMounted == 1) {
			strcpy(tmp_set, "unmount");
	    } else {
			strcpy(tmp_set, "mount");
	    }
		strcat(tmp_set, " /cache");
	}
	if (mInt == MNT_SDCARD)
	{
	    if (sdcIsMounted == 1) {
			strcpy(tmp_set, "unmount");
	    } else {
			strcpy(tmp_set, "mount");
	    }
		strcat(tmp_set, " /sdcard");
	}
	if (mInt == MNT_SDEXT)
	{
		if (stat(sde.blk,&st) != 0)
		{
			strcpy(tmp_set, "-------");
			sdeIsMounted = -1;
		} else {
		    if (sdeIsMounted == 1) {
				strcpy(tmp_set, "unmount");
		    } else {
				strcpy(tmp_set, "mount");
		    }
		}
		strcat(tmp_set, " /sd-ext");
	}
	return tmp_set;
}

void mount_menu(int pIdx)
{
	chkMounts();
	
	const char* MENU_MNT_HEADERS[] = {  "Mount Menu",
										"Pick a Partition to Mount:",
										NULL };
	
	char* MENU_MNT[] = { isMounted(MNT_SYSTEM),
						 isMounted(MNT_DATA),
						 isMounted(MNT_CACHE),
						 isMounted(MNT_SDCARD),
						 isMounted(MNT_SDEXT),
						 "<-- Back To Main Menu",
						 NULL };
	
	char** headers = prepend_title(MENU_MNT_HEADERS);
	
	inc_menu_loc(MNT_BACK);
	for (;;)
	{
		int chosen_item = get_menu_selection(headers, MENU_MNT, 0, pIdx);
		pIdx = chosen_item;
		switch (chosen_item)
		{
		case MNT_SYSTEM:
			if (sysIsMounted == 0)
			{
				__system("mount /system");
				ui_print("/system has been mounted.\n");
			} else if (sysIsMounted == 1) {
				__system("umount /system");
				ui_print("/system has been unmounted.\n");
			}
			break;
		case MNT_DATA:
			if (datIsMounted == 0)
			{
				__system("mount /data");
				ui_print("/data has been mounted.\n");
			} else if (datIsMounted == 1) {
				__system("umount /data");
				ui_print("/data has been unmounted.\n");
			}
			break;
		case MNT_CACHE:
			if (cacIsMounted == 0)
			{
				__system("mount /cache");
				ui_print("/cache has been mounted.\n");
			} else if (cacIsMounted == 1) {
				__system("umount /cache");
				ui_print("/cache has been unmounted.\n");
			}
			break; 
		case MNT_SDCARD:
			if (sdcIsMounted == 0)
			{
				__system("mount /sdcard");
				ui_print("/sdcard has been mounted.\n");
			} else if (sdcIsMounted == 1) {
				__system("umount /sdcard");
				ui_print("/sdcard has been unmounted.\n");
			}
			break;
		case MNT_SDEXT:
			if (sdeIsMounted == 0)
			{
				__system("mount /sd-ext");
				ui_print("/sd-ext has been mounted.\n");
			} else if (sdeIsMounted == 1) {
				__system("umount /sd-ext");
				ui_print("/sd-ext has been unmounted.\n");
			}
			break;
		case MNT_BACK:
			dec_menu_loc();
			return;
		}
	    break;
	}
	ui_end_menu();
    dec_menu_loc();
    mount_menu(pIdx);
}

void main_wipe_menu()
{
	#define MAIN_WIPE_CACHE           0
	#define MAIN_WIPE_DALVIK   	  	  1
	#define MAIN_WIPE_DATA            2
	#define ITEM_BATTERY_STATS     	  3
	#define ITEM_ROTATE_DATA       	  4
	#define MAIN_WIPE_BACK            5

    const char* MENU_MAIN_WIPE_HEADERS[] = {  "Wipe Menu",
    										  "Wipe Front to Back:",
                                              NULL };
    
	char* MENU_MAIN_WIPE[] = { "Wipe Cache",
	                           "Wipe Dalvik Cache",
	                           "Wipe Everything (Data Factory Reset)",
		                       "Wipe Battery Stats",
		                       "Wipe Rotation Data",
	                           "<-- Back To Main Menu",
	                           NULL };

    char** headers = prepend_title(MENU_MAIN_WIPE_HEADERS);

    int isSdExt = 0;
    struct stat st;
    if (stat("/sd-ext",&st) == 0)
    {
    	__system("mount /sd-ext");
    	isSdExt = 1;
    }
    
    inc_menu_loc(MAIN_WIPE_BACK);
    for (;;)
    {
//	ui_set_background(BACKGROUND_ICON_WIPE_CHOOSE);
        int chosen_item = get_menu_selection(headers, MENU_MAIN_WIPE, 0, 0);
        switch (chosen_item)
        {
            case MAIN_WIPE_DALVIK:
                wipe_dalvik_cache();
                break;

            case MAIN_WIPE_CACHE:
   //         	ui_set_background(BACKGROUND_ICON_WIPE);
                ui_print("\n-- Wiping Cache Partition...\n");
                erase_volume("/cache");
                ui_print("-- Cache Partition Wipe Complete!\n");
  //              ui_set_background(BACKGROUND_ICON_WIPE_CHOOSE);
                if (!ui_text_visible()) return;
                break;

            case MAIN_WIPE_DATA:
                wipe_data(ui_text_visible());
   //             ui_set_background(BACKGROUND_ICON_WIPE_CHOOSE);
                if (!ui_text_visible()) return;
                break;

            case ITEM_BATTERY_STATS:
                wipe_battery_stats();
                break;

            case ITEM_ROTATE_DATA:
                wipe_rotate_data();
                break;
                
            case MAIN_WIPE_BACK:
            	dec_menu_loc();
 //               ui_set_background(BACKGROUND_ICON_MAIN);
            	return;
        }
	    if (go_home) { 
	        dec_menu_loc();
   //             ui_set_background(BACKGROUND_ICON_MAIN);
	        return;
	    }
        break;
    }
	ui_end_menu();
        dec_menu_loc();
    //    ui_set_background(BACKGROUND_ICON_MAIN);
	main_wipe_menu();
}



void run_script(const char *str1, const char *str2, const char *str3, const char *str4, const char *str5, const char *str6, const char *str7, int request_confirm)
{
	ui_print("%s", str1);
        ui_clear_key_queue();
	ui_print("\nPress Power to confirm,");
       	ui_print("\nany other key to abort.\n");
	int confirm;
	if (request_confirm) // this option is used to skip the confirmation when the gui is in use
		confirm = ui_wait_key();
	else
		confirm = KEY_POWER;
	
		if (confirm == BTN_MOUSE || confirm == KEY_POWER || confirm == SELECT_ITEM) {
                	ui_print("%s", str2);
		        pid_t pid = fork();
                	if (pid == 0) {
                		char *args[] = { "/sbin/sh", "-c", (char*)str3, "1>&2", NULL };
                	        execv("/sbin/sh", args);
                	        fprintf(stderr, str4, strerror(errno));
                	        _exit(-1);
                	}
			int status;
			while (waitpid(pid, &status, WNOHANG) == 0) {
				ui_print(".");
               		        sleep(1);
			}
                	ui_print("\n");
			if (!WIFEXITED(status) || (WEXITSTATUS(status) != 0)) {
                		ui_print("%s", str5);
                	} else {
                		ui_print("%s", str6);
                	}
		} else {
	       		ui_print("%s", str7);
       	        }
		if (!ui_text_visible()) return;
}


void check_and_run_script(const char* script_file, const char* display_name)
{
	// Check for and run startup script if script exists
	struct statfs st;
	if (statfs(script_file, &st) == 0) {
		ui_print("Running %s script...\n", display_name);
		char command[255];
		strcpy(command, "chmod 755 ");
		strcat(command, script_file);
		__system(command);
		__system(script_file);
		ui_print("\nFinished running %s script.\n", display_name);
	}
}
