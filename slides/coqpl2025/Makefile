coqpl2025/index.html: Makefile
	echo '<html>' > coqpl2025/index.html
	echo '<header><title>CoqPL 2025</title></header>' >> coqpl2025/index.html
	echo '<body><H1>CoqPL 2025</H1>' >> coqpl2025/index.html
	echo '<H3>Elpi: rule-based meta-languge for Rocq</H3>' >> coqpl2025/index.html
	echo '<p>Slides: <a href="slides.pdf">pdf</a> <a href="html/">html</a></p>' >> coqpl2025/index.html
	echo '</body></html>' >> coqpl2025/index.html

coqpl2025/slides.pdf: slides.md Makefile
	npm exec slidev -- export --with-clicks --output coqpl2025/slides.pdf

coqpl2025/html: slides.md Makefile
	npm exec slidev -- build --out coqpl2025/html --base /members/Enrico.Tassi/coqpl2025/html/

upload: coqpl2025/slides.pdf coqpl2025/html coqpl2025/index.html
	scp -Cr coqpl2025/ roquableu.inria.fr:/net/servers/www-sop/members/Enrico.Tassi/
	@echo
	@echo 'https://www-sop.inria.fr/members/Enrico.Tassi/coqpl2025/'
