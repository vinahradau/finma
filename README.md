# CIDFINMA

# Formalization of client identifying data regulation requirements for banks in Switzerland

This project contains the formal specification of CID FINMA regulation. The specification is written using the Z notation and Alloy and was developed by Serge (Siarhei Vinahradau, vinahradau@yahoo.de).

The CID FINMA regulation was published by the Swiss Financial Market Supervisory Authority (FINMA) and describes the requirements to handling client identifying data (CID) by banks in Switzerland (S. References below). The document is available in German.

This Z specification can be animated using the jaza animator. Jaza is available for download as an executable on github, thanks to Mark Utting (S. References).

# Project Contents

1. CIDFINMA_spec_Z.zed16 file with the Z schema definitions and operations. The file can be opened and edited with the CZT editor (S. References).
2. CIDFINMA_spec_Z.zed with the contents of the *.zed16 file (above) converted into the latex notation. This *.zed file can be loaded into the jaza animator. Converted into latex by CZT and slightly modified manually to comply with jaza syntax expectations.
3. Descriptions of the use cases, jaza command line arguments and outputs to test the CID FINMA specification:
    - jaza/CIDFINMA_spec_Z_jaza_case_1_1.txt;
    - jaza/CIDFINMA_spec_Z_jaza_case_1_2.txt;
    - jaza/CIDFINMA_spec_Z_jaza_case_2_1.txt;
    - jaza/CIDFINMA_spec_Z_jaza_case_2_2.txt;
4. CIDFINMA_spec_Z.pdf with Z shemas and operations in a user friendly format.
5. CIDFINMA_spec_Z_schema_description.pdf with schema comments.
6. cid_domain_specification_alloy.als: Alloy specification. To be executed within the Alloy Analyzer GUI.

# References

FINMA-Rundschreiben „Operationelle Risiken – Banken“ (published in 20.11.2008, last updated in 2017). https://www.finma.ch/de/~/media/finma/dokumente/rundschreiben-archiv/finma-rs-200821---30-06-2017.pdf

Jaza Animator: https://github.com/uho/jaza

CZT IDE: http://czt.sourceforge.net/
 
Alloy Analyzer: https://alloytools.org/
