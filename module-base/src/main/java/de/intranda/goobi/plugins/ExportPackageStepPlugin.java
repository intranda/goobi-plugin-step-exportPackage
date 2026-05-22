package de.intranda.goobi.plugins;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.Writer;
import java.nio.file.DirectoryStream;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

/**
 * This file is part of a plugin for Goobi - a Workflow tool for the support of mass digitization.
 *
 * Visit the websites for more information.
 *          - https://goobi.io
 *          - https://www.intranda.com
 *          - https://github.com/intranda/goobi
 *
 * This program is free software; you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free
 * Software Foundation; either version 2 of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with this program; if not, write to the Free Software Foundation, Inc., 59
 * Temple Place, Suite 330, Boston, MA 02111-1307 USA
 *
 */

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.UUID;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

import javax.xml.XMLConstants;
import javax.xml.transform.Source;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.stream.StreamResult;
import javax.xml.transform.stream.StreamSource;

import org.apache.commons.configuration.HierarchicalConfiguration;
import org.apache.commons.configuration.SubnodeConfiguration;
import org.apache.commons.lang.StringUtils;
import org.goobi.beans.Process;
import org.goobi.beans.Step;
import org.goobi.production.enums.LogType;
import org.goobi.production.enums.PluginGuiType;
import org.goobi.production.enums.PluginReturnValue;
import org.goobi.production.enums.PluginType;
import org.goobi.production.enums.StepReturnValue;
import org.goobi.production.plugin.interfaces.IStepPluginVersion2;
import org.jdom2.Document;
import org.jdom2.Element;
import org.jdom2.JDOMException;
import org.jdom2.Namespace;
import org.jdom2.input.SAXBuilder;
import org.jdom2.output.Format;
import org.jdom2.output.XMLOutputter;
import org.joda.time.DateTime;

import de.sub.goobi.config.ConfigPlugins;
import de.sub.goobi.export.download.ExportMets;
import de.sub.goobi.helper.Helper;
import de.sub.goobi.helper.StorageProvider;
import de.sub.goobi.helper.VariableReplacer;
import de.sub.goobi.helper.exceptions.DAOException;
import de.sub.goobi.helper.exceptions.ExportFileException;
import de.sub.goobi.helper.exceptions.SwapException;
import de.sub.goobi.helper.exceptions.UghHelperException;
import lombok.Getter;
import lombok.extern.log4j.Log4j2;
import net.xeoh.plugins.base.annotations.PluginImplementation;
import ugh.exceptions.DocStructHasNoTypeException;
import ugh.exceptions.MetadataTypeNotAllowedException;
import ugh.exceptions.PreferencesException;
import ugh.exceptions.ReadException;
import ugh.exceptions.TypeNotAllowedForParentException;
import ugh.exceptions.WriteException;

@PluginImplementation
@Log4j2
public class ExportPackageStepPlugin implements IStepPluginVersion2 {

    private static final long serialVersionUID = -5795680118749183317L;
    @Getter
    private String title = "intranda_step_exportPackage";
    @Getter
    private Step step;
    private Process process;
    private String target;
    private String returnPath;
    private boolean useSubFolderPerProcess = true;
    private boolean createZipPerProcess = true;
    private boolean copyInternalMetaFile = true;
    private Map<String, String> imagefolders = new HashMap<>();
    private boolean includeOcr = false;
    private boolean includeSource = false;
    private boolean includeImport = false;
    private boolean includeExport = false;
    private boolean includeITM = false;
    private boolean includeValidation = false;
    private boolean transformMetaFile = false;
    private String transformMetaFileXsl = "";
    private String transformMetaFileResultFileName = "";
    private boolean transformMetsFile = false;
    private String transformMetsFileXsl = "";
    private String transformMetsFileResultFileName = "";

    private String checksumValidationCommand = "";
    private String checksumFileExtension = "";
    private String checksumType = "";
    private boolean includeUUID = false;
    private boolean includeChecksum = false;
    private String fileGroupReplacement;
    private String folderNameRule;

    private static final Namespace mets = Namespace.getNamespace("mets", "http://www.loc.gov/METS/");
    private static final Namespace xlink = Namespace.getNamespace("xlink", "http://www.w3.org/1999/xlink");

    @Override
    public void initialize(Step step, String returnPath) {
        this.returnPath = returnPath;
        this.step = step;
        process = step.getProzess();
        // read parameters from correct block in configuration file
        SubnodeConfiguration myconfig = ConfigPlugins.getProjectAndStepConfig(title, step);
        target = myconfig.getString("target", "/opt/digiverso/export/");

        List<HierarchicalConfiguration> imageFolderConfig = myconfig.configurationsAt("imagefolder");
        for (HierarchicalConfiguration hc : imageFolderConfig) {
            imagefolders.put(hc.getString("."), hc.getString("@filegroup"));
        }

        useSubFolderPerProcess = myconfig.getBoolean("useSubFolderPerProcess", true);
        createZipPerProcess = myconfig.getBoolean("createZipPerProcess", false);
        if (createZipPerProcess) {
            // createZipPerProcess requires useSubFolderPerProcess to be true;
            useSubFolderPerProcess = true;
        }
        copyInternalMetaFile = myconfig.getBoolean("copyInternalMetaFile", true);

        folderNameRule = myconfig.getString("folderNameRule", null);

        includeOcr = myconfig.getBoolean("ocr", false);
        includeSource = myconfig.getBoolean("source", false);
        includeImport = myconfig.getBoolean("import", false);
        includeExport = myconfig.getBoolean("export", false);
        includeITM = myconfig.getBoolean("itm", false);
        includeValidation = myconfig.getBoolean("validation", false);
        includeUUID = myconfig.getBoolean("uuid", false);
        includeChecksum = myconfig.getBoolean("checksum", false);
        fileGroupReplacement = myconfig.getString("fileGroupReplacement");

        checksumValidationCommand = myconfig.getString("checksumValidationCommand", "/usr/bin/sha1sum");
        checksumFileExtension = myconfig.getString("checksumFileExtension", ".sha1");
        if (StringUtils.isNotBlank(checksumFileExtension) && !checksumFileExtension.startsWith(".")) {
            checksumFileExtension = "." + checksumFileExtension;
        }
        checksumType = myconfig.getString("checksumType", "SHA-1");

        transformMetaFile = myconfig.getBoolean("transformMetaFile", false);
        transformMetaFileXsl = myconfig.getString("transformMetaFileXsl", "/opt/digiverso/goobi/package_meta.xsl");
        transformMetaFileResultFileName = myconfig.getString("transformMetaFileResultFileName",
                "resultFromInternalMets.xml");
        transformMetsFile = myconfig.getBoolean("transformMetsFile", false);
        transformMetsFileXsl = myconfig.getString("transformMetsFileXsl", "/opt/digiverso/goobi/package_mets.xsl");
        transformMetsFileResultFileName = myconfig.getString("transformMetsFileResultFileName", "resultFromMets.xml");

        log.info("GeneratePackage step plugin initialized");
    }

    @Override
    public PluginGuiType getPluginGuiType() {
        return PluginGuiType.NONE;
    }

    @Override
    public String getPagePath() {
        return null;
    }

    @Override
    public PluginType getType() {
        return PluginType.Step;
    }

    @Override
    public String cancel() {
        return "/uii" + returnPath;
    }

    @Override
    public String finish() {
        return "/uii" + returnPath;
    }

    @Override
    public int getInterfaceVersion() {
        return 0;
    }

    @Override
    public HashMap<String, StepReturnValue> validate() {
        return null;
    }

    @Override
    public boolean execute() {
        PluginReturnValue ret = run();
        return ret != PluginReturnValue.ERROR;
    }

    @Override
    public PluginReturnValue run() {
        boolean successful = false;
        List<Path> checksumFiles = null;
        if (includeChecksum) {
            Path folder;
            try {
                folder = Paths.get(process.getProcessDataDirectory(), "validation", "checksum", "images");
                if (StorageProvider.getInstance().isDirectory(folder)) {
                    checksumFiles = StorageProvider.getInstance().listFiles(folder.toString(), checksumFilter);
                } else {
                    includeChecksum = false;
                }
            } catch (IOException | SwapException e) {
                log.error(e);
                includeChecksum = false;
            }
        }
        VariableReplacer variableReplacer = null;

        try {
            variableReplacer = new VariableReplacer(process.readMetadataFile().getDigitalDocument(),
                    process.getRegelsatz().getPreferences(), process, step);
        } catch (PreferencesException | ReadException | IOException | SwapException e1) {
            log.info(e1);
            variableReplacer = new VariableReplacer(null, null, process, step);
        }
        // first make sure that the destination folder exists
        Path destination = Paths.get(target);
        String folderName = null;
        if (useSubFolderPerProcess) {

            if (StringUtils.isBlank(folderNameRule)) {
                destination = Paths.get(target, process.getTitel());
            } else {
                folderName = folderNameRule;
                if (folderName.contains("{timestamp}")) {
                    String dateFormat = getDateFormat(System.currentTimeMillis());
                    folderName = folderNameRule.replace("{timestamp}", dateFormat);
                }
                folderName = variableReplacer.replace(folderName);
                destination = Paths.get(target, folderName);
            }
        }
        if (!Files.exists(destination)) {
            try {
                Files.createDirectories(destination);
            } catch (IOException e) {
                log.error("Error during generation of destination path", e);
                Helper.addMessageToProcessJournal(process.getId(), LogType.ERROR,
                        "Error during generation of destination path: " + e.getMessage());
            }
        }

        // do the regular export of the METS file
        ExportMets em = new ExportMets();
        try {
            successful = em.startExport(process, destination.toString() + FileSystems.getDefault().getSeparator());
        } catch (PreferencesException | WriteException | DocStructHasNoTypeException | MetadataTypeNotAllowedException
                | ReadException | TypeNotAllowedForParentException | IOException | InterruptedException
                | ExportFileException | UghHelperException | SwapException | DAOException e) {
            log.error("Error during METS export in package generation", e);
            Helper.addMessageToProcessJournal(process.getId(), LogType.ERROR,
                    "Error during METS export in package generation: " + e.getMessage());
            Helper.setFehlerMeldung("Error during METS export in package generation", e);
        }

        // export images folders as well
        try {
            for (String f : imagefolders.keySet()) {
                Path folder = Paths.get(process.getConfiguredImageFolder(f));
                if (StorageProvider.getInstance().isFileExists(folder)) {
                    Path currentDestination = Paths.get(destination.toString(), folder.getFileName().toString());
                    StorageProvider.getInstance().copyDirectory(folder, currentDestination);
                    if (includeChecksum) {
                        if (!validateExportedFolder(checksumFiles, folder, currentDestination)) {
                            // validation not successful, try it again
                            StorageProvider.getInstance().copyDirectory(folder, currentDestination);
                            if (!validateExportedFolder(checksumFiles, folder, currentDestination)) {
                                // validation still not successful, maybe checksums are outdated?, abort
                                Helper.addMessageToProcessJournal(process.getId(), LogType.ERROR,
                                        "checksum missmatch on export");
                                return PluginReturnValue.ERROR;
                            }

                        }
                    }
                }
            }
        } catch (IOException | InterruptedException | SwapException | DAOException e) {
            successful = false;
            log.error("Error during folder export in package generation", e);
            Helper.addMessageToProcessJournal(process.getId(), LogType.ERROR,
                    "Error during folder export in package generation: " + e.getMessage());
        }

        try {

            // copy the internal meta.xml file
            if (copyInternalMetaFile) {
                StorageProvider.getInstance()
                        .copyFile(Paths.get(process.getMetadataFilePath()),
                                Paths.get(destination.toString(), process.getTitel() + "_meta.xml"));
            }

            // export ocr results
            if (includeOcr) {
                Path ocrFolder = Paths.get(process.getOcrDirectory());
                if (ocrFolder != null && Files.exists(ocrFolder)) {
                    List<Path> ocrData = StorageProvider.getInstance().listFiles(ocrFolder.toString());
                    for (Path path : ocrData) {
                        if (Files.isDirectory(path)) {
                            StorageProvider.getInstance()
                                    .copyDirectory(path,
                                            Paths.get(destination.toString(), path.getFileName().toString()));
                        } else {
                            StorageProvider.getInstance()
                                    .copyFile(path,
                                            Paths.get(destination.toString(), path.getFileName().toString()));
                        }
                    }
                }
            }

            // export source folder
            if (includeSource) {
                Path sourceFolder = Paths.get(process.getSourceDirectory());
                if (sourceFolder != null && Files.exists(sourceFolder)) {
                    StorageProvider.getInstance()
                            .copyDirectory(sourceFolder,
                                    Paths.get(destination.toString(), process.getTitel() + "_source"));
                }
            }

            // export import folder
            if (includeImport) {
                Path importFolder = Paths.get(process.getImportDirectory());
                if (importFolder != null && Files.exists(importFolder)) {
                    StorageProvider.getInstance()
                            .copyDirectory(importFolder,
                                    Paths.get(destination.toString(), process.getTitel() + "_import"));
                }
            }

            // export export folder
            if (includeExport) {
                Path exportFolder = Paths.get(process.getExportDirectory());
                if (exportFolder != null && Files.exists(exportFolder)) {
                    StorageProvider.getInstance()
                            .copyDirectory(exportFolder,
                                    Paths.get(destination.toString(), process.getTitel() + "_export"));
                }
            }

            // export ITM folder
            if (includeITM) {
                Path itmFolder = Paths.get(process.getProcessDataDirectory() + "taskmanager");
                if (itmFolder != null && Files.exists(itmFolder)) {
                    StorageProvider.getInstance()
                            .copyDirectory(itmFolder,
                                    Paths.get(destination.toString(), itmFolder.getFileName().toString()));
                }
            }

            // export validation folder
            if (includeValidation) {
                Path validationFolder = Paths.get(process.getProcessDataDirectory() + "validation");
                if (validationFolder != null && Files.exists(validationFolder)) {
                    StorageProvider.getInstance()
                            .copyDirectory(validationFolder,
                                    Paths.get(destination.toString(), validationFolder.getFileName().toString()));
                }
            }
            Path metsFile = Paths.get(destination.toString(), process.getTitel() + "_mets.xml");
            if (includeUUID) {
                // open exported file
                Document document = readDocument(metsFile);

                Element root = document.getRootElement();
                Element fileSec = root.getChild("fileSec", mets);
                List<Element> fileGroups = fileSec.getChildren();

                // - UUIDs as @ID for each mets:fileGrp and mets:file within
                Map<String, String> idMap = new HashMap<>();
                for (Element fileGroup : fileGroups) {
                    // create new UUID for fileGrp @ID
                    UUID uuid = UUID.randomUUID();
                    fileGroup.setAttribute("ID", uuid.toString());

                    // create new UUID for each file and store it in ID attribute
                    for (Element file : fileGroup.getChildren()) {
                        String oldId = file.getAttributeValue("ID");
                        String newId = UUID.randomUUID().toString();
                        file.setAttribute("ID", newId);
                        // save mapping from old to new id
                        idMap.put(oldId, newId);
                    }
                }
                // - update fptr, link to uuids
                List<Element> structMaps = root.getChildren("structMap", mets);
                for (Element structMap : structMaps) {
                    if ("PHYSICAL".equals(structMap.getAttributeValue("TYPE"))) {
                        Element physSequence = structMap.getChild("div", mets);
                        List<Element> pages = physSequence.getChildren();
                        for (Element page : pages) {
                            List<Element> filePointer = page.getChildren("fptr", mets);
                            for (Element fptr : filePointer) {
                                String oldId = fptr.getAttributeValue("FILEID");

                                String newId = idMap.get(oldId);
                                if (StringUtils.isNotBlank(newId)) {
                                    fptr.setAttribute("FILEID", newId);
                                }
                            }
                        }
                    }
                }
                // save exported file
                writeDocument(document, metsFile);
            }
            if (includeChecksum) {
                // check if checksum file exists
                Path folder = Paths.get(process.getProcessDataDirectory(), "validation", "checksum", "images");
                if (StorageProvider.getInstance().isDirectory(folder)) {

                    // open exported file
                    Document document = readDocument(metsFile);
                    Element root = document.getRootElement();
                    Element fileSec = root.getChild("fileSec", mets);
                    List<Element> fileGroups = fileSec.getChildren();
                    for (Element fileGroup : fileGroups) {
                        Path checksumFile = null;
                        // find checksum file for current filegroup
                        for (String imageFolderName : imagefolders.keySet()) {
                            String fileGroupName = imagefolders.get(imageFolderName);
                            if (fileGroupName != null && fileGroupName.equals(fileGroup.getAttributeValue("USE"))) {
                                Path imageFolder = Paths.get(process.getConfiguredImageFolder(imageFolderName));
                                for (Path checksum : checksumFiles) {
                                    if (checksum.getFileName()
                                            .toString()
                                            .replace(checksumFileExtension, "")
                                            .equals(imageFolder.getFileName().toString())) {
                                        checksumFile = checksum;
                                    }
                                }
                            }
                        }
                        if (checksumFile != null) {
                            // read checksums
                            Map<String, String> filesAndChecksums = new HashMap<>();
                            List<String> lines = Files.readAllLines(checksumFile);
                            for (String line : lines) {
                                if (!line.startsWith("#") && StringUtils.isNotBlank(line)) {
                                    String[] parts = line.split("  ");
                                    filesAndChecksums.put(parts[1].substring(0, parts[1].lastIndexOf(".")), parts[0]);
                                }
                            }
                            // add checksum + type for each file element
                            for (Element file : fileGroup.getChildren()) {
                                Element location = file.getChild("FLocat", mets);
                                String ref = location.getAttributeValue("href", xlink);
                                String filename = ref.contains("/") ? ref.substring(ref.lastIndexOf("/") + 1) : ref;
                                String basename = filename.substring(0, filename.lastIndexOf("."));
                                String checksum = filesAndChecksums.get(basename);
                                if (StringUtils.isNotBlank(checksum)) {
                                    file.setAttribute("CHECKSUMTYPE", checksumType);
                                    file.setAttribute("CHECKSUM", checksum);
                                }
                            }
                        }
                    }

                    // save exported file
                    writeDocument(document, metsFile);
                }
            }

            if (StringUtils.isNotBlank(fileGroupReplacement) && StringUtils.isNotBlank(folderName)) {
                String searchValue = variableReplacer.replace(fileGroupReplacement);
                // open exported file
                Document document = readDocument(metsFile);

                Element root = document.getRootElement();
                Element fileSec = root.getChild("fileSec", mets);
                List<Element> fileGroups = fileSec.getChildren();
                for (Element fileGroup : fileGroups) {
                    for (Element file : fileGroup.getChildren()) {
                        Element location = file.getChild("FLocat", mets);
                        String ref = location.getAttributeValue("href", xlink);
                        ref = ref.replace(searchValue, folderName);
                        location.setAttribute("href", ref, xlink);
                    }
                }

                // save exported file
                writeDocument(document, metsFile);
            }

            // do XSLT Transformation of METS file
            if (transformMetsFile) {
                Source xslt = new StreamSource(new File(transformMetsFileXsl));
                Source mets = new StreamSource(metsFile.toFile());
                TransformerFactory factory = TransformerFactory.newInstance();
                factory.setAttribute(XMLConstants.ACCESS_EXTERNAL_DTD, "");
                factory.setAttribute(XMLConstants.ACCESS_EXTERNAL_STYLESHEET, "");
                Transformer transformer = factory.newTransformer(xslt);
                transformer.setParameter("processTitle", process.getTitel());
                transformer.transform(mets, new StreamResult(
                        new File(destination.toFile(), variableReplacer.replace(transformMetsFileResultFileName))));
            }

            // do XSLT Transformation of internal METS file
            if (transformMetaFile) {
                Source xslt = new StreamSource(new File(transformMetaFileXsl));
                Source mets = new StreamSource(
                        Paths.get(destination.toString(), process.getTitel() + "_meta.xml").toFile());
                TransformerFactory factory = TransformerFactory.newInstance();
                factory.setAttribute(XMLConstants.ACCESS_EXTERNAL_DTD, "");
                factory.setAttribute(XMLConstants.ACCESS_EXTERNAL_STYLESHEET, "");
                Transformer transformer = factory.newTransformer(xslt);
                transformer.transform(mets, new StreamResult(
                        new File(destination.toFile(), variableReplacer.replace(transformMetaFileResultFileName))));
            }

            if (createZipPerProcess) {
                Path sourceFolder = destination;
                Path zipDestination = destination.getParent();
                zipDestination = zipDestination.resolve(sourceFolder.getFileName() + ".zip");

                try {
                    OutputStream os = Files.newOutputStream(zipDestination);
                    ZipOutputStream zos = new ZipOutputStream(os);

                    //DELETE the folder if creating the archive was successful
                    if (zipFolder(zos, sourceFolder, sourceFolder.getParent())) {
                        StorageProvider.getInstance().deleteDir(sourceFolder);
                    }

                    zos.flush();
                    os.flush();
                    zos.close();
                    os.close();

                } catch (IOException ex) {
                    String message = "Error creating Zip-File";
                    log.error(message + "!", ex);
                    Helper.addMessageToProcessJournal(process.getId(), LogType.ERROR,
                            message + ": " + ex.getMessage());
                }
            }

        } catch (SwapException | DAOException | IOException | TransformerException e) {
            successful = false;
            log.error("Error during additional folder export in package generation", e);
            Helper.addMessageToProcessJournal(process.getId(), LogType.ERROR,
                    "Error during additional folder export in package generation: " + e.getMessage());
        }

        log.info("GeneratePackage step plugin executed");
        if (!successful) {
            return PluginReturnValue.ERROR;
        }
        return PluginReturnValue.FINISH;
    }

    /**
     * Creates a zip file of the files in the source folder
     *
     * @param zos a zipoutputstream to write to
     * @param source the source folder of the files that shall be compressed
     * @param parentDirectory the parent directory of the source folder needed to create relative paths
     * @return returns true if the operation was successful
     */
    static boolean zipFolder(ZipOutputStream zos, Path source, Path parentDirectory) {
        if (source == null || !Files.exists(source)) {
            return false;
        }
        if (Files.isDirectory(source)) {
            try (DirectoryStream<Path> stream = Files.newDirectoryStream(source)) {
                // Add entry for empty folders!
                Iterator<Path> itr = stream.iterator();
                if (!itr.hasNext()) {
                    String folderWithSeparator = parentDirectory.relativize(source).toString() + File.separator;
                    zos.putNextEntry(new ZipEntry(folderWithSeparator));
                    zos.closeEntry();
                }
                while (itr.hasNext()) {
                    zipFolder(zos, itr.next(), parentDirectory);
                }
                return true;
            } catch (IOException e) {
                e.printStackTrace();
                return false;
            }
        } else {
            try {
                InputStream is = Files.newInputStream(source);
                byte[] buffer = new byte[1024];
                ZipEntry entry = new ZipEntry(parentDirectory.relativize(source).toString());

                zos.putNextEntry(entry);

                int length;
                while ((length = is.read(buffer)) > 0) {
                    zos.write(buffer, 0, length);
                }
                zos.closeEntry();
                is.close();
            } catch (IOException e) {
                e.printStackTrace();
                return false;
            }
            return true;
        }
    }

    static String getDateFormat(long currentTimeMillis) {

        DateTime dt = new DateTime(currentTimeMillis);

        int year = dt.getYear();
        int month = dt.getMonthOfYear();
        int day = dt.getDayOfMonth();
        int hours = dt.getHourOfDay();
        int min = dt.getMinuteOfHour();
        int sec = dt.getSecondOfMinute();

        StringBuilder formattedDate = new StringBuilder();
        formattedDate.append(year);
        if (month < 10) {
            formattedDate.append("0");
        }
        formattedDate.append(month);
        if (day < 10) {
            formattedDate.append("0");
        }
        formattedDate.append(day);
        formattedDate.append("_");
        if (hours < 10) {
            formattedDate.append("0");
        }
        formattedDate.append(hours);

        if (min < 10) {
            formattedDate.append("0");
        }
        formattedDate.append(min);

        if (sec < 10) {
            formattedDate.append("0");
        }
        formattedDate.append(sec);

        return formattedDate.toString();
    }

    /**
     * validation of the exported files.
     * 
     * returns false, if the files don't match against previous created checksum file or true in all other cases (validation successful, no checksum
     * file found)
     * 
     * @param checksumFiles
     * @param folder
     * @param currentDestination
     * @return
     * @throws IOException
     * @throws InterruptedException
     */

    private boolean validateExportedFolder(List<Path> checksumFiles, Path folder, Path currentDestination)
            throws IOException, InterruptedException {
        for (Path checksumFile : checksumFiles) {
            if (checksumFile.getFileName()
                    .toString()
                    .replace(checksumFileExtension, "")
                    .equals(folder.getFileName().toString())) {
                // found checksum file for current folder
                ProcessBuilder builder = new ProcessBuilder().directory(currentDestination.toFile())
                        .command(checksumValidationCommand, "--check", "--quiet", checksumFile.toString());
                java.lang.Process validation = builder.start();
                int response = validation.waitFor();
                if (response != 0) {
                    InputStream stdErr = validation.getErrorStream();
                    LinkedList<String> result = new LinkedList<>();
                    try (Scanner inputLines = new Scanner(stdErr)) {
                        while (inputLines.hasNextLine()) {
                            String myLine = inputLines.nextLine();
                            result.add(myLine);
                        }
                    } finally {
                        if (stdErr != null) {
                            stdErr.close();
                        }
                    }
                    return false;
                }
            }
        }
        return true;
    }

    private static Document readDocument(Path path) {
        SAXBuilder builder = new SAXBuilder();
        Document document = null;
        try {
            document = builder.build(path.toFile());
        } catch (JDOMException | IOException e) {
            log.error(e);
        }
        return document;
    }

    private static void writeDocument(Document document, Path path) {
        XMLOutputter xmlOutput = new XMLOutputter();
        xmlOutput.setFormat(Format.getPrettyFormat());
        try (Writer w = new FileWriter(path.toString())) {
            xmlOutput.output(document, w);
        } catch (IOException e) {
            log.error(e);
        }
    }

    private DirectoryStream.Filter<Path> checksumFilter = new DirectoryStream.Filter<>() {
        @Override
        public boolean accept(Path entry) throws IOException {
            return entry.getFileName().toString().endsWith(checksumFileExtension);
        }
    };

}
