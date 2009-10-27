



%.o : %.c
	$(CC) $(CFLAGS) $(CINCLUDES) -c $< -o $@